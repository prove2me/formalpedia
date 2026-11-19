-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCollectionChild_child_iteration_native
-- name    : Lax263307Proofs.NativeCollectionChild.child_iteration_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:23.269922+00:00
-- url     : https://prove2.me/theorems/4e10ec38-93e4-443e-9318-243f6d450156
-- title:
--   Execute a heavy collection child and restore its parent
-- statement:
--   Let a native collection state contain a selected component $C$, target, union and recursive context. Assume the full frame, child graph, search, mask, LP and rounded-normalization workspace guards. Suppose the smaller-fuel recursive child has the source's bounded execution contract, with at most $s$ transitions and time $t$. The fixed parent handlers push the frame, perform that child execution, restore the parent, and process its optional answer:
--   $$\operatorname{parent}_{\rm out}=\operatorname{collectReply}(\operatorname{childAnswer}).$$
--   The complete result predicate, collection anchor and explicit segment bounds are retained. The child execution is a premise of this composition theorem.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCollectionChild.lean, theorem Lax263307Proofs.NativeCollectionChild.child_iteration, line 47

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax263307Proofs.NativeCollectionChild
end Lax263307Proofs.NativeCollectionChild

theorem Lax263307Proofs.NativeCollectionChild.child_iteration_native : ∀ {n : Nat} (B S D k r fuel i target childSteps childTime : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x : Fin n → NNRat)
  (parts : List (Finset (Fin n))) (A C U : Finset (Fin n)) (extent : String → Nat) (front : List Nat)
  (answer : Option (Finset (Fin (@Finset.card (Fin n) C)))),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                      (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                  n)
                i)
              target)
            fuel)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (Lax263307Proofs.NativeCatalogMetadata.N n r)))
        (@OfNat.ofNat Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      B →
    @LT.lt Nat instLTNat
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
        B →
      (∀ (a : String),
          @Membership.mem String (List String) (@List.instMembership String)
              (Lax263307Proofs.NativeCoreMachine.frameArrays cfg) a →
            @Eq Nat (extent a) S) →
        @LE.le Nat instLENat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
            (extent "recursion.frames") →
          @LE.le Nat instLENat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))
              (extent "child.graph") →
            @LE.le Nat instLENat
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))
                (extent "search.graph") →
              @LE.le Nat instLENat (@Finset.card (Fin n) C) (extent "subset.bits") →
                @LE.le Nat instLENat
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (Lax263307Proofs.NativeCatalogMetadata.N n r))
                    (extent "lp.input") →
                  @LE.le Nat instLENat
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (Lax263307Proofs.NativeCatalogMetadata.N n r))
                      (extent "round.normal") →
                    ∀ (σ : Lax808846Proofs.Imp.Env),
                      @Lax263307Proofs.NativeCollectionContext.Context n B D k r fuel S G inst x parts A extent front
                          σ →
                        @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                            (fun (v : Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v)) C σ →
                          @Eq Nat (σ.vars "component.mask") (@Lax263307Proofs.NativeMasks.mask n C) →
                            @Eq Nat (σ.vars "component.target") target →
                              @Eq Nat (σ.vars "component.i") i →
                                @Eq Nat (σ.vars "component.union") (@Lax263307Proofs.NativeMasks.mask n U) →
                                  @Eq Nat (σ.vars "machine.running")
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                    @Eq Nat (σ.vars "machine.phase")
                                        (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) →
                                      @Lax263307Proofs.NativeCollectionChild.Recursive n B S fuel childSteps childTime
                                          cfg G inst C target front σ answer →
                                        ∃ (τ : Lax808846Proofs.Imp.Env) (steps : Nat) (total : Nat),
                                          And
                                            (Lax263307Proofs.NativeMachineSegment.Segment B
                                              (Lax263307Proofs.NativeCoreMachine.phases cfg) steps total σ τ)
                                            (And
                                              (@LE.le Nat instLENat steps
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) childSteps
                                                  (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                              (And
                                                (@LE.le Nat instLENat total
                                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                    (@OfNat.ofNat Nat (nat_lit 16)
                                                                      (instOfNatNat (nat_lit 16)))
                                                                    S)
                                                                  (@OfNat.ofNat Nat (nat_lit 8)
                                                                    (instOfNatNat (nat_lit 8))))
                                                                (@List.length String
                                                                  (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@OfNat.ofNat Nat (nat_lit 7)
                                                                  (instOfNatNat (nat_lit 7)))
                                                                (@List.length String
                                                                  (Lax263307Proofs.NativeCoreMachine.frameScalars
                                                                    cfg))))
                                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                              (@OfNat.ofNat Nat (nat_lit 52)
                                                                (instOfNatNat (nat_lit 52)))
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))))
                                                          (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                                        childTime)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@OfNat.ofNat Nat (nat_lit 16)
                                                                  (instOfNatNat (nat_lit 16)))
                                                                S)
                                                              (@OfNat.ofNat Nat (nat_lit 16)
                                                                (instOfNatNat (nat_lit 16))))
                                                            (@List.length String
                                                              (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                            (@OfNat.ofNat Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                                            (@List.length String
                                                              (Lax263307Proofs.NativeCoreMachine.frameScalars cfg))))
                                                        (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@OfNat.ofNat Nat (nat_lit 45) (instOfNatNat (nat_lit 45)))
                                                          (@Finset.card (Fin n) C))
                                                        (@OfNat.ofNat Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                              (@OfNat.ofNat Nat (nat_lit 28)
                                                                (instOfNatNat (nat_lit 28)))
                                                              n)
                                                            (@OfNat.ofNat Nat (nat_lit 104)
                                                              (instOfNatNat (nat_lit 104))))
                                                          (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                                        (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                                                (And (Lax263307Proofs.NativeCollectionAnchor.Anchor σ τ)
                                                  (@Option.casesOn (Finset (Fin (@Finset.card (Fin n) C)))
                                                    (fun (x : Option (Finset (Fin (@Finset.card (Fin n) C)))) =>
                                                      (fun (answer : Option (Finset (Fin (@Finset.card (Fin n) C)))) =>
                                                          Prop)
                                                        x)
                                                    answer
                                                    ((fun (_ : Unit) =>
                                                        @Lax263307Proofs.NativeCollectionTrace.ResultOutput n
                                                          (@Lax263307Proofs.NativeCollectionContext.Context n B D k r
                                                            fuel S G inst x parts A extent front)
                                                          (fun (C : Finset (Fin n)) (u : Nat)
                                                              (τ : Lax808846Proofs.Imp.Env) =>
                                                            Lax455465Proofs.RamVirtualState.Prefix
                                                              (@Lax263307Proofs.NativeRoundedQuery.normal
                                                                (Lax263307.MomentLP.dimension n r)
                                                                (@Lax263307.RationalCutBuffer.integerNormal
                                                                  (Lax263307.MomentLP.dimension n r)
                                                                  (@Lax263307.RoundedOracleSearch.rationalNormal
                                                                    (Lax263307.MomentLP.dimension n r)
                                                                    (@Lax263307Proofs.NativeComponentNormal.normal n r A
                                                                      C u))))
                                                              "round.normal" τ)
                                                          (@Lax263307.ComputedRounding.Result.cut n C
                                                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) target
                                                              (@OfNat.ofNat Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          τ)
                                                      Unit.unit)
                                                    fun (val : Finset (Fin (@Finset.card (Fin n) C))) =>
                                                    (fun (I : Finset (Fin (@Finset.card (Fin n) C))) =>
                                                        @Lax263307Proofs.NativeCollectionTrace.At n
                                                          (@Lax263307Proofs.NativeCollectionContext.Context n B D k r
                                                            fuel S G inst x parts A extent front)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i
                                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                          (@Union.union (Finset (Fin n))
                                                            (@Finset.instUnion (Fin n) (instDecidableEqFin n)) U
                                                            (@Finset.image (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                              (instDecidableEqFin n)
                                                              (@DFunLike.coe
                                                                (@OrderEmbedding (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                                  (@instLEFin (@Finset.card (Fin n) C)) (@instLEFin n))
                                                                (Fin (@Finset.card (Fin n) C))
                                                                (fun (x : Fin (@Finset.card (Fin n) C)) => Fin n)
                                                                (@instFunLikeOrderEmbedding
                                                                  (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                                  (@instLEFin (@Finset.card (Fin n) C)) (@instLEFin n))
                                                                (@Lax263307.ComputedSeparators.label n C))
                                                              I))
                                                          τ)
                                                      val)))) := by sorry
