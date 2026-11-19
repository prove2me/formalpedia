-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRegionCore_iteration_spec_native
-- name    : Lax455465Proofs.RamRegionCore.iteration_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:19.045027+00:00
-- url     : https://prove2.me/theorems/6a3ac7e6-462e-4ccb-9d2e-399be1cec7f7
-- title:
--   One complete native region-growth iteration
-- statement:
--   Fix a rational network instance, its rational metric, the seed and threshold data, and the active-set/history state appearing in this interface. Assume its complete coefficient-height, dimension, positivity, word-size and allocated-storage guards. The fixed command implements one functional region-growth iteration, with the explicit instruction bound from the source:
--
--   $$\mathrm{Spec}_B(\mathrm{RegionState}_s,c_{\rm step},\mathrm{Output}_{\operatorname{step}(s)},T_{\rm step}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionCore.lean, theorem iteration_spec (lines 31–138)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamRegionCore
end Lax455465Proofs.RamRegionCore

theorem Lax455465Proofs.RamRegionCore.iteration_spec_native : ∀ (B M H : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n)
  (length : Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold : NNRat) (p : Nat)
  (active : Finset (Fin n)) (history : List (Lax455465Proofs.RamRegionRecord.Entry n)),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat (Lax455465Proofs.RegionBudget.steps p) M →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          B →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
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
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax455465Proofs.RegionBudget.steps p)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  B →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history))
                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    B →
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold) →
                    (∀ (v : Fin n),
                        @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M) →
                      (∀ (v : Fin n),
                          @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M) →
                        (∀ (u v : Fin n),
                            @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M) →
                          (∀ (u v : Fin n),
                              @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M) →
                            (∀ (u v : Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v))) →
                              Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta) →
                                Lax455465Proofs.LpInputSize.Height M
                                    (@NNRat.cast Rat Rat.instNNRatCast
                                      (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                                        (@Nat.cast NNRat
                                          (@AddMonoidWithOne.toNatCast NNRat
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                              (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                                (@Semiring.toNonAssocSemiring NNRat
                                                  (@DivisionSemiring.toSemiring NNRat
                                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                                          (Lax455465Proofs.RegionBudget.steps p)))) →
                                  (∀ (root : Fin n) (i : Nat)
                                      (hi :
                                        @LT.lt Nat instLTNat i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v : Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as : List NNRat) (i : Nat) =>
                                              @LT.lt Nat instLTNat i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v : Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H) →
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta)) →
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed) →
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta) →
                                          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              p →
                                            (∀ (u v w : Fin n),
                                                @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                  (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length v w)))) →
                                              @LE.le Rat Rat.instLE
                                                  (@Lax455465Proofs.RegionRounding.metricCost n I
                                                    (@Lax455465Proofs.MetricMatrix.rational n length))
                                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                    (@Nat.cast Rat Rat.instNatCast p)
                                                    (@NNRat.cast Rat Rat.instNNRatCast seed)) →
                                                @LE.le Nat instLENat
                                                    (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history) p →
                                                  Lax808846Proofs.Reasoning.Spec B
                                                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p σ)
                                                        (And
                                                          (@Lax455465Proofs.RamRegionInvariant.Dynamic n active history
                                                            σ)
                                                          (Lax455465Proofs.RamRegionInvariant.Room n p σ)))
                                                    Lax455465Proofs.RamRegionLoop.iteration
                                                    (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p τ)
                                                        (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                          (@Lax455465Proofs.RamRegionCore.Output n I length seed beta
                                                            delta threshold p active history τ)))
                                                    (Lax455465Proofs.RamRegionCore.cost n p M H) := by sorry
