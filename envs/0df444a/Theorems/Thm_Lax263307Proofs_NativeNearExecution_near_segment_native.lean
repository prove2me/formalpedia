-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeNearExecution_near_segment_native
-- name    : Lax263307Proofs.NativeNearExecution.near_segment_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:48.410762+00:00
-- url     : https://prove2.me/theorems/6d0f8218-22f5-4df4-8ca2-a55d5ed8bd26
-- title:
--   Complete native near-branch segment with child executions
-- statement:
--   Fix the native core configuration, graph, rational near point and recursive child procedure. Assume the complete near-branch setup, oracle context, stored rounded state and required bounded child executions. The actual phase machine returns the functional near reply, preserves the rounded state, context and root frame, and satisfies the published transition and time bounds:
--
--   $$\mathrm{reply}_{\rm out}=\operatorname{NearOracle}(\mathrm{flow},G,x,\mathrm{child}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNearExecution.lean, theorem near_segment (lines 133–287)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeNearExecution
end Lax263307Proofs.NativeNearExecution

theorem Lax263307Proofs.NativeNearExecution.near_segment_native : ∀ {n r : Nat} (D k p b load F fuel S v limit M h T w space flowTime childSteps childTime : Nat)
  (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (flow : List Nat → List Nat)
  (x : Fin (Lax263307Proofs.NativeCatalogMetadata.N n r) → Rat) (extent : String → Nat) (front : List Nat)
  (child : (C : Finset (Fin n)) → Nat → Option (Finset (Fin (@Finset.card (Fin n) C)))),
  Lax263307Proofs.NativeNearExecution.Bounds n r D k p M h T fuel S w cfg extent front →
    (∀ (i : Fin (Lax263307Proofs.NativeCatalogMetadata.N n r)),
        Lax263307Proofs.NativeSignedArithmetic.Bounded M (x i)) →
      (∀ (A : Finset (Fin n)),
          @Eq (Option (Finset (Fin n)))
              (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                (@Lax263307.MomentLP.decode Rat n r x))
              (@Option.some (Finset (Fin n)) A) →
            @LE.le Nat instLENat (@Finset.card (Fin n) A) r) →
        (∀ (A : Finset (Fin n)),
            @Eq (Option (Finset (Fin n)))
                (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                  (@Lax263307.MomentLP.decode Rat n r x))
                (@Option.some (Finset (Fin n)) A) →
              ∀ (C : Finset (Fin n)),
                @LE.le Nat instLENat
                  (Lax263307.ComputedRounding.target
                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                      (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D))
                    (∑ v ∈ C,
                      @NNRat.cast Rat Rat.instNNRatCast
                        (@Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A v)))
                  T) →
          (∀ (a : String),
              @Membership.mem String (List String) (@List.instMembership String)
                  Lax263307Proofs.NativeSeparatorContext.workspace a →
                @LE.le Nat instLENat space (extent a)) →
            (∀ (A : Finset (Fin n)),
                have costs := @Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A;
                have cs :=
                  @Lax263307.ComputedSeparators.cuts n (@Lax263307.ComputedSeparators.step n flow G inst costs b load k)
                    n (@Finset.univ (Fin n) (Fin.fintype n));
                Lax808846Proofs.Reasoning.Spec
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                  (fun (σ : Lax808846Proofs.Imp.Env) =>
                    And (@Lax263307Proofs.NativeSeparatorContext.Context n G inst costs b load k space σ)
                      (@LE.le Nat instLENat
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@List.length Nat (σ.arrs "separator.pieces"))))
                  (Lax263307Proofs.NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                    And (@Lax263307Proofs.NativeSeparatorContext.Context n G inst costs b load k space τ)
                      (And
                        (@Eq Nat (τ.vars "separator.remaining")
                          (@Lax263307Proofs.NativeMasks.mask n
                            (@Lax263307.ComputedSeparators.remaining n (@Finset.univ (Fin n) (Fin.fintype n)) cs)))
                        (And
                          (@Eq Nat (τ.vars "separator.value")
                            (@Lax263307Proofs.NativeMasks.mask n (@Lax263307.ComputedSeparators.separator n cs)))
                          (And
                            (@Eq Nat (τ.vars "separator.count")
                              (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))
                            (And
                              (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeCutRecords.words n cs)
                                "separator.cuts" τ)
                              (And
                                (@Eq Nat (τ.vars "separator.position")
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeCutPieces.words n cs)
                                  "separator.pieces" τ)))))))
                  flowTime) →
              (∀ (A : Finset (Fin n)),
                  @Eq (Option (Finset (Fin n)))
                      (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                        (@Lax263307.MomentLP.decode Rat n r x))
                      (@Option.some (Finset (Fin n)) A) →
                    let costs := @Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A;
                    let cs :=
                      @Lax263307.ComputedSeparators.cuts n
                        (@Lax263307.ComputedSeparators.step n flow G inst costs b load k) n
                        (@Finset.univ (Fin n) (Fin.fintype n));
                    ∀ (i : Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))),
                      @Membership.mem (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                          (List (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))
                          (@List.instMembership
                            (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))
                          (Lax263307.NearOracle.order (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)) i →
                        @LT.lt Rat Rat.instLT
                            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                              (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@Nat.cast Rat Rat.instNatCast D))
                                (@Nat.cast Rat Rat.instNatCast k))
                              (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                (@Nat.cast Rat Rat.instNatCast n)))
                            (∑ v ∈ @Lax263307.ComputedSeparators.pieces n cs i,
                              @NNRat.cast Rat Rat.instNNRatCast (costs v)) →
                          ∀ (base σ : Lax808846Proofs.Imp.Env),
                            Lax263307Proofs.NativeOracleContext.Protocol
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                D S v cfg extent front σ →
                              @Lax263307Proofs.NativeCollectionExecution.Invariant n
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                  D k r fuel S G inst costs
                                  (@List.map (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                    (Finset (Fin n)) (@Lax263307.ComputedSeparators.pieces n cs)
                                    (Lax263307.NearOracle.order
                                      (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                  A extent front base σ →
                                @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                                    (fun (v : Fin n) => @NNRat.cast Rat Rat.instNNRatCast (costs v))
                                    (@Lax263307.ComputedSeparators.pieces n cs i) σ →
                                  @Eq Nat (σ.vars "component.mask")
                                      (@Lax263307Proofs.NativeMasks.mask n
                                        (@Lax263307.ComputedSeparators.pieces n cs i)) →
                                    @Eq Nat (σ.vars "component.target")
                                        (Lax263307.ComputedRounding.target
                                          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                            (@Nat.cast Rat Rat.instNatCast D))
                                          (∑ v ∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                            @NNRat.cast Rat Rat.instNNRatCast (costs v))) →
                                      @Eq Nat (σ.vars "machine.running")
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                        @Eq Nat (σ.vars "machine.phase")
                                            (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) →
                                          @Lax263307Proofs.NativeCollectionChild.Recursive n
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                            S fuel childSteps childTime cfg G inst
                                            (@Lax263307.ComputedSeparators.pieces n cs i)
                                            (Lax263307.ComputedRounding.target
                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                (@Nat.cast Rat Rat.instNatCast D))
                                              (∑ v ∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                                @NNRat.cast Rat Rat.instNNRatCast (costs v)))
                                            front σ
                                            (child (@Lax263307.ComputedSeparators.pieces n cs i)
                                              (Lax263307.ComputedRounding.target
                                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                  (@OfNat.ofNat Rat (nat_lit 1)
                                                    ((have costs :=
                                                        @Lax263307.NearOracle.costs n r
                                                          (@Lax263307.MomentLP.decode Rat n r x) A;
                                                      have cs :=
                                                        @Lax263307.ComputedSeparators.cuts n
                                                          (@Lax263307.ComputedSeparators.step n flow G inst costs b load
                                                            k)
                                                          n (@Finset.univ (Fin n) (Fin.fintype n));
                                                      fun
                                                        (i :
                                                          Option
                                                            (Fin
                                                              (@List.length (Prod (Finset (Fin n)) (Finset (Fin n)))
                                                                cs)))
                                                        (base σ : Lax808846Proofs.Imp.Env) =>
                                                      @Rat.instOfNat (nat_lit 1))
                                                      i base σ))
                                                  (@Nat.cast Rat Rat.instNatCast D))
                                                (∑ v ∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                                  @NNRat.cast Rat Rat.instNNRatCast (costs v))))) →
                ∀ (j : Nat) (state : Lax263307.RoundedOracleSearch.State (Lax263307Proofs.NativeCatalogMetadata.N n r))
                  (σ : Lax808846Proofs.Imp.Env),
                  @Lax263307Proofs.NativeOracleContext.Context n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                      D k r p b load F fuel S v limit cfg G inst extent front σ →
                    @Lax263307Proofs.NativeRoundedTrace.StoredState (Lax263307Proofs.NativeCatalogMetadata.N n r) j
                        state σ →
                      Lax455465Proofs.RamVirtualState.Prefix
                          (@Lax109476.RationalEncoding.encodeVector (Lax263307Proofs.NativeCatalogMetadata.N n r) x)
                          "lp.word" σ →
                        @Eq Nat (σ.vars "machine.running") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                          @Eq Nat (σ.vars "machine.phase") (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) →
                            ∃ (τ : Lax808846Proofs.Imp.Env) (transitions : Nat) (total : Nat),
                              And
                                (Lax263307Proofs.NativeMachineSegment.Segment
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                  (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ)
                                (And
                                  (@LE.le Nat instLENat transitions
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) childSteps
                                          (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                                  (And
                                    (@LE.le Nat instLENat total
                                      (Lax263307Proofs.NativeNearExecution.timeBound cfg n r M S h childTime flowTime))
                                    (And
                                      (@Lax263307Proofs.NativeOracleContext.Context n
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                        D k r p b load F fuel S v limit cfg G inst extent front τ)
                                      (And
                                        (@Lax263307Proofs.NativeRoundedTrace.StoredState
                                          (Lax263307Proofs.NativeCatalogMetadata.N n r) j state τ)
                                        (And
                                          (@Lax263307Proofs.NativeNearExecution.Output n r
                                            (@Lax263307Proofs.NativeNearExecution.run n r flow G inst D k p b load
                                              (@Lax263307.MomentLP.decode Rat n r x) child)
                                            τ)
                                          (Lax263307Proofs.NativeOracleContext.RootData σ τ)))))) := by sorry
