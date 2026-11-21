-- Prove2me | Theorems.Thm_MasulloRH_single_prime_height_test_without_log_loss
-- name    : MasulloRH.single_prime_height_test_without_log_loss
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:39:51.293275+00:00
-- url     : https://prove2.me/theorems/39fb0995-3fd6-4f25-8ff9-df4c41fe9df4
-- title:
--   A finite prime certificate gives a height test with inverse-power tail allowance
-- statement:
--   For N at least 196 a single certificate with slack ε verifies the critical line through every height H satisfying 2.00000001(ε+7/N^(3/2))(1+H²)<4.
-- source:
--   New consequence of the dyadic prime estimates and zeta quartet exclusion.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology MeasureTheory

namespace MasulloRH
theorem single_prime_height_test_without_log_loss (N : ℕ) (hN : 196 ≤ N) (ε : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    ∀ F : Finset Z, C+(∑ j ∈ Finset.range (N+1), f j) ≤ M F + ε →
      ∀ H : ℝ, (200000001/100000000 : ℝ)*(ε+7/(N:ℝ)^(3/2:ℝ))*(1+H^2) < 4 →
        ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2 := by sorry
end MasulloRH
