-- Prove2me | Theorems.Thm_Lax109476Proofs_RamFeasibilitySetup_setup_spec_native
-- name    : Lax109476Proofs.RamFeasibilitySetup.setup_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:12.696948+00:00
-- url     : https://prove2.me/theorems/e5d9939d-43a0-4161-b325-6dfeb336e3a4
-- title:
--   Prepare a stored integer system for exact ellipsoid feasibility
-- statement:
--   Let $P$ be an integer system with $m+n\le S$, and suppose every matrix and right-hand-side coefficient has magnitude at most $2^{2S}$. At every host width meeting the explicit feasibility-setup bound, the fixed command constructs the normalized integer matrix, rational right-hand side and search budget:
--   $$(A',b',N)=\operatorname{normalize}(P,\operatorname{outerScale},\operatorname{precision},\operatorname{thresholdSteps}+1).$$
--   From its full stored input predicate, it returns the complete initialized search-input predicate within $T_{\rm setup}(S)$ instructions. The coordinate cap, normalization scale, precision denominator and budget are computed by the command.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFeasibilitySetup.lean, theorem Lax109476Proofs.RamFeasibilitySetup.setup_spec, line 31

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamFeasibilitySetup
end Lax109476Proofs.RamFeasibilitySetup

theorem Lax109476Proofs.RamFeasibilitySetup.setup_spec_native : ∀ (m n S w : Nat) (P : Lax109476.LinearProgram.Program Int m n),
  @LE.le Nat instLENat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n) S →
    (∀ (i : Fin m) (j : Fin n),
        @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.A Int m n P i j).natAbs
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              S))) →
      (∀ (i : Fin m),
          @LE.le Nat instLENat (@Lax109476.LinearProgram.Program.b Int m n P i).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S))) →
        @LE.le Nat instLENat (Lax109476Proofs.RamFeasibilitySetup.wordWidth S) w →
          Lax808846Proofs.Reasoning.Spec
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            (@Lax109476Proofs.RamFeasibilitySetup.Input m n P S) Lax109476Proofs.RamFeasibilitySetup.setup
            (fun (x τ : Lax808846Proofs.Imp.Env) =>
              @Lax109476Proofs.RamSearchBounds.Input (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n) n
                (@Lax109476Proofs.NormalizedFeasibility.normalizedMatrix m n P
                  (Lax109476Proofs.NormalizedFeasibility.outerScale n
                    (Lax109476Proofs.IntegerCertificates.coordinateCap m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S)))))
                (@Lax109476Proofs.NormalizedFeasibility.normalizedBound m n P
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                    (@Nat.cast Rat Rat.instNatCast
                      (Lax109476Proofs.NormalizedFeasibility.precisionDenominator m n
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S))))))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (Lax109476Proofs.EllipsoidSequence.thresholdSteps n
                    (Lax109476Proofs.NormalizedFeasibility.ballExponent m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S))))
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                τ)
            (Lax109476Proofs.RamFeasibilitySetup.instructionBound S) := by sorry
