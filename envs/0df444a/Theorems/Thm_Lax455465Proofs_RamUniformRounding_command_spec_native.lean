-- Prove2me | Theorems.Thm_Lax455465Proofs_RamUniformRounding_command_spec_native
-- name    : Lax455465Proofs.RamUniformRounding.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:21.980199+00:00
-- url     : https://prove2.me/theorems/bd2f2d7c-53cc-48ac-b1d3-2a1705e64fcf
-- title:
--   Polynomial native execution of metric region rounding
-- statement:
--   Let $I$ be a rational network instance and $d$ its nonnegative rational metric. Assume positive support and total weight, zero diagonal, triangle inequalities, distance separation at least one, and metric height bounded by the polynomial input-size exponent $P(L)$. Under the stated polynomial word budget and complete region workspace, the fixed rounding command returns the specified region-cut output within its polynomial clock:
--
--   $$\mathrm{Spec}_{2^W}(\mathrm{MetricInput}_{I,d},\mathrm{round},\mathrm{RegionCutOutput}_{I,d},T_P(L)).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamUniformRounding.lean, theorem command_spec (lines 53–82)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamUniformRounding
end Lax455465Proofs.RamUniformRounding

theorem Lax455465Proofs.RamUniformRounding.command_spec_native : ∀ (P : @Polynomial Nat Nat.instSemiring) {n : Nat} (kind : Lax455465.ProductNetwork.EdgeKind)
  (I : Lax455465.RationalEncoding.RationalInstance n) (d : Lax455465Proofs.MetricMatrix.Matrix n),
  (∀ (u v : Fin n),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (@NNRat.cast Rat Rat.instNNRatCast (d u v))) →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Lax455465Proofs.RamRoundingInit.support n (@Lax455465.RationalEncoding.RationalInstance.weight n I)) →
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
                (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                  (@NNRat.cast Rat Rat.instNNRatCast (d v t)))) →
            @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                  (@Lax455465Proofs.MetricMatrix.rational n d)) →
              ∀ (W : Nat),
                @LE.le Nat instLENat
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.wordBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P)))
                    W →
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
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
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.timeBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P))) := by sorry
