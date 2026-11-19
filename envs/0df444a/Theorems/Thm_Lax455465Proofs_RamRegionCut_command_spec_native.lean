-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRegionCut_command_spec_native
-- name    : Lax455465Proofs.RamRegionCut.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:36.979022+00:00
-- url     : https://prove2.me/theorems/23229e9e-82bf-4e6d-b62f-fa76b70d14fb
-- title:
--   Extract the cut from a completed region process
-- statement:
--   Fix a rational network instance, its rational metric, the seed and threshold data, and the active-set/history state appearing in this interface. Assume its complete coefficient-height, dimension, positivity, word-size and allocated-storage guards. The fixed command implements the specified cut masks, admissibility data and quantitative cut-output predicate, with the explicit instruction bound from the source:
--
--   $$\mathrm{Spec}_B(\mathrm{CompletedRegion},c_{\rm cut},\mathrm{CutOutput},T_{\rm cut}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionCut.lean, theorem command_spec (lines 30–103)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamRegionCut
end Lax455465Proofs.RamRegionCut

theorem Lax455465Proofs.RamRegionCut.command_spec_native : ∀ (B M : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n) (d : Lax455465Proofs.MetricMatrix.Matrix n)
  (seed beta delta threshold : NNRat) (p : Nat) (s : Lax455465Proofs.RegionRuntimeState.State n),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p)
        M →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          B →
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) B →
          @LT.lt Nat instLTNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) p)
                (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              B →
            @LT.lt Nat instLTNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                B →
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  B →
                (∀ (u w : Fin n), Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (d u w))) →
                  (∀ (e : Lax455465Proofs.RamRegionRecord.Entry n),
                      @Membership.mem (Lax455465Proofs.RamRegionRecord.Entry n)
                          (List (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@List.instMembership (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@Lax455465Proofs.RegionRuntimeState.State.history n s) e →
                        Lax455465Proofs.LpInputSize.Height M
                          (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465Proofs.RamRegionRecord.Entry.radius n e))) →
                    (∀ (Tin Tout : Finset (Fin n)) (hin : @Finset.Nonempty (Fin n) Tin)
                        (hout : @Finset.Nonempty (Fin n) Tout),
                        @Lax455465Proofs.LargePotentialData.Bounds n I d Tin Tout hin hout M) →
                      (∀ (S : Finset (Fin n)), @Lax455465Proofs.CutScoreHeight.Bounds n I S M) →
                        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                            (@Lax455465Proofs.LargeBallRounding.total n I) →
                          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
                            (∀ (v : Fin n),
                                @Eq NNRat (d v v)
                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                    (@Zero.toOfNat0 NNRat
                                      (@MulZeroClass.toZero NNRat
                                        (@instMulZeroClassOfSemiring NNRat
                                          (@DivisionSemiring.toSemiring NNRat
                                            (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))) →
                              @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                                    (@Lax455465Proofs.MetricMatrix.rational n d)) →
                                (∀ (u v w : Fin n),
                                    @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u w))
                                      (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                        (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                                        (@NNRat.cast Rat Rat.instNNRatCast (d v w)))) →
                                  @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast seed)
                                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                        (@Lax455465Proofs.RegionRounding.metricCost n I
                                          (@Lax455465Proofs.MetricMatrix.rational n d))
                                        (@Nat.cast Rat Rat.instNatCast p)) →
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast delta)
                                        (@Lax455465Proofs.RegionRounding.radiusBudget n I) →
                                      @Lax455465Proofs.RegionRuntimeCorrespondence.ValidFinal n I d seed delta p s →
                                        Lax808846Proofs.Reasoning.Spec B
                                          (fun (σ : Lax808846Proofs.Imp.Env) =>
                                            And
                                              (@Lax455465Proofs.RamRegionInvariant.Fixed n I d seed beta delta threshold
                                                p σ)
                                              (And (@Lax455465Proofs.RamRegionState.View n I d seed beta s σ)
                                                (And
                                                  (Lax455465Proofs.RamUnsignedScalar.Stored "round.total"
                                                    (@Lax455465Proofs.RamRoundingInit.total n
                                                      (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                                    σ)
                                                  (Lax455465Proofs.RamRegionCut.Room n σ))))
                                          Lax455465Proofs.RamRegionCut.command
                                          (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                            @Lax455465Proofs.RamRegionCut.Output n I d p τ)
                                          (Lax455465Proofs.RamRegionCut.cost n p M) := by sorry
