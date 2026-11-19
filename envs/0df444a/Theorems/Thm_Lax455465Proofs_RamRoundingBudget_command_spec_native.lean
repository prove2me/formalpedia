-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRoundingBudget_command_spec_native
-- name    : Lax455465Proofs.RamRoundingBudget.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:16.895323+00:00
-- url     : https://prove2.me/theorems/c2a89faf-90af-4509-93bb-b611866a8edb
-- title:
--   Guard the complete native metric-rounding execution
-- statement:
--   Let $I$ be a valid rational flow instance with at least two supported endpoints and $d$ a stored metric satisfying the source's separation and shortest-distance conditions. Suppose the rational data and metric meet the specified height bounds, the host width meets the uniform rounding bound, and all source, metric, region and cut buffers satisfy their full input predicate. The fixed rounding command returns its complete cut output within the explicit uniform instruction bound:
--   $$\operatorname{Spec}_{2^W}(\operatorname{Input}_{I,d},\operatorname{round},\operatorname{Output}_{I,d},T).$$
--   The source output predicate includes admissibility, the flow-or-cut ratio guarantee and exact stored membership flags; all intermediate radius and potential guards are derived from the input bounds.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRoundingBudget.lean, theorem Lax455465Proofs.RamRoundingBudget.command_spec, line 47

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamRoundingBudget
end Lax455465Proofs.RamRoundingBudget

theorem Lax455465Proofs.RamRoundingBudget.command_spec_native : ∀ (W w : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n) (d : Lax455465Proofs.MetricMatrix.Matrix n),
  @LE.le Nat instLENat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      w →
    @LE.le Nat instLENat (Lax455465Proofs.RamRoundingBudget.width n w) W →
      (∀ (v : Fin n),
          Lax455465Proofs.LpInputSize.Height
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465.RationalEncoding.RationalInstance.weight n I v))) →
        (∀ (u v : Fin n),
            Lax455465Proofs.LpInputSize.Height
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
              (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v))) →
          (∀ (u v : Fin n),
              Lax455465Proofs.LpInputSize.Height
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                (@NNRat.cast Rat Rat.instNNRatCast (d u v))) →
            Lax455465Proofs.LpInputSize.Height
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465Proofs.MetricCostData.cost n I d)) →
              (∀ (i : Nat),
                  Lax455465Proofs.LpInputSize.Height
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                    (@NNRat.cast Rat Rat.instNNRatCast
                      (@List.sum NNRat
                        (@Distrib.toAdd NNRat
                          (@instDistribOfSemiring NNRat
                            (@DivisionSemiring.toSemiring NNRat
                              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))
                        (@MulZeroClass.toZero NNRat
                          (@instMulZeroClassOfSemiring NNRat
                            (@DivisionSemiring.toSemiring NNRat
                              (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))
                        (@List.take NNRat i
                          (@List.ofFn NNRat n (@Lax455465.RationalEncoding.RationalInstance.weight n I)))))) →
                @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@Lax455465Proofs.RamRoundingInit.support n
                      (@Lax455465.RationalEncoding.RationalInstance.weight n I)) →
                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                      (@Lax455465Proofs.LargeBallRounding.total n I) →
                    (∀ (v : Fin n),
                        @Eq NNRat (d v v)
                          (@OfNat.ofNat NNRat (nat_lit 0)
                            (@Zero.toOfNat0 NNRat
                              (@MulZeroClass.toZero NNRat
                                (@instMulZeroClassOfSemiring NNRat
                                  (@DivisionSemiring.toSemiring NNRat
                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))) →
                      (∀ (u v t : Fin n),
                          @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u t))
                            (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                              (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                              (@NNRat.cast Rat Rat.instNNRatCast (d v t)))) →
                        @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                            (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                              (@Lax455465Proofs.MetricMatrix.rational n d)) →
                          Lax808846Proofs.Reasoning.Spec
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
                            (fun (σ : Lax808846Proofs.Imp.Env) =>
                              And (@Lax455465Proofs.RamMetricRounding.Input n I d σ)
                                (And
                                  (Lax455465Proofs.RamRegionInvariant.Room n
                                    (@Lax455465Proofs.RamRoundingInit.support n
                                      (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                    σ)
                                  (Lax455465Proofs.RamRegionCut.Room n σ)))
                            Lax455465Proofs.RamMetricRounding.command
                            (fun (x τ : Lax808846Proofs.Imp.Env) =>
                              @Lax455465Proofs.RamRegionCut.Output n I d
                                (@Lax455465Proofs.RamRoundingInit.support n
                                  (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                τ)
                            (Lax455465Proofs.RamRoundingBudget.cost n
                              (@Lax455465Proofs.RamRoundingInit.support n
                                (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                              w
                              (@Lax455465Proofs.RamRoundingInit.total n
                                (@Lax455465.RationalEncoding.RationalInstance.weight n I))) := by sorry
