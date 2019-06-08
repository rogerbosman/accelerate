  Permute     :: (Shape sh, Shape sh', Elt e)
              => PreFun     acc aenv (e -> e -> e)              -- combination function
              -> acc            aenv (Array sh' e)              -- default values
              -> PreFun     acc aenv (sh -> sh')                -- permutation function
              -> acc            aenv (Array sh e)               -- source array
              -> PreOpenAcc acc aenv (Array sh' e)


Permute f        d        p a

*call cvtF on combination and permutation function*

  -- Conversions for closed scalar functions and expressions. This just
  -- applies scalar simplifications.
  --
  cvtF :: PreFun acc aenv' t -> PreFun acc aenv' t
  cvtF = simplify

  *typeclass defined in Data.Array.Accelerate.Trafo.Simplify*
  *seems "unimportant" for the functionality i'm after*

*partially apply into2 with permute and the optimized funs*
  permute f p d a     = Permute f d p a
  *permute swaps the default values and permutation function. Is this just some
   glue to "repair" some function calling args in wrong order? Seems weird*

*into2 "sinks" the given optimized funs into an env. But as we partially apply,
 we now get a fun that given an env, sinks the funs and applies the permute
 function above*
 -- Sink a term from one array environment into another, where additional
 -- bindings have come into scope according to the witness and no old things have
 -- vanished.
 --
 sink :: Sink f => Extend acc env env' -> f env t -> f env' t
 sink env = weaken (k env)
   where
     k :: Extend acc env env' -> Idx env t -> Idx env' t
     k BaseEnv       = Stats.substitution "sink" id
     k (PushEnv e _ ) = SuccIdx . k

  **I don't know what sink actually does**

*now we call embed2, which just calls trav2 with id id*
  embed2 :: forall aenv as bs cs. (Arrays as, Arrays bs, Arrays cs)
         => (forall aenv'. Extend acc aenv aenv' -> acc aenv' as -> acc aenv' bs -> PreOpenAcc acc aenv' cs)
         ->       acc aenv as
         ->       acc aenv bs
         -> Embed acc aenv cs
  embed2 = trav2 id id

  *ops:
      f1 = id
      f0 = id
      op = the partially applied into2 that sinks and applies permute given an env

      Embed env1 cc1 = (f1 . embedAcc) d* **(our default values)**
     *Embed env0 cc0 = (f0 . embedAcc . sink env1) a* **(our source array)**
  *k*
  trav2 :: forall aenv as bs cs. (Arrays as, Arrays bs, Arrays cs)
        => (forall aenv'. Embed acc aenv' as -> Embed acc aenv' as)
        -> (forall aenv'. Embed acc aenv' bs -> Embed acc aenv' bs)
        -> (forall aenv'. Extend acc aenv aenv' -> acc aenv' as -> acc aenv' bs -> PreOpenAcc acc aenv' cs)
        ->       acc aenv as
        ->       acc aenv bs
        -> Embed acc aenv cs
  trav2 f1 f0 op (f1 . embedAcc -> Embed env1 cc1) (f0 . embedAcc . sink env1 -> Embed env0 cc0)
    | env     <- env1 `append` env0
    , acc1    <- inject . compute' $ sink env0 cc1
    , acc0    <- inject . compute' $ cc0
    = Embed (env `PushEnv` inject (op env acc1 acc0)) (Done ZeroIdx)
