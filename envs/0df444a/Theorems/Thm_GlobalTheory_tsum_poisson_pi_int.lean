-- Prove2me | Theorems.Thm_GlobalTheory_tsum_poisson_pi_int
-- name    : GlobalTheory.tsum_poisson_pi_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:51.108918+00:00
-- url     : https://prove2.me/theorems/7dda704a-9308-4787-bb65-8739b27181ca
-- title:
--   Global Theory: tsum poisson pi int
-- statement:
--   The Global Theory construction uses the tsum poisson pi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L198-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean#L198-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.tsum_poisson_pi_int {f F : (ι → ℝ) → ℂ} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : (ι → ℤ) → ℝ, Summable g ∧ ∀ (n : ι → ℤ) (u : ι → ℝ), ‖u‖ ≤ R →
      ‖f ((fun i => (n i : ℝ)) + u)‖ ≤ g n)
    (hF : ∀ y : ι → ℝ, ∫ x : ι → ℝ,
      cexp (-(2 * π * I) * ((fun i => (x i : ℂ)) ⬝ᵥ fun i => (y i : ℂ))) * f x = F y)
    (hs : Summable fun n : ι → ℤ => ‖F fun i => (n i : ℝ)‖) (u : ι → ℝ) :
    ∑' n : ι → ℤ, f ((fun i => (n i : ℝ)) + u) =
      ∑' n : ι → ℤ, cexp (2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (u i : ℂ))) *
        F fun i => (n i : ℝ) := by sorry
