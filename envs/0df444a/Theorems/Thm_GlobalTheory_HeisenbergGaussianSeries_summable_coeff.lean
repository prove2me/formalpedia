-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_summable_coeff
-- name    : GlobalTheory.HeisenbergGaussianSeries.summable_coeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:12.947905+00:00
-- url     : https://prove2.me/theorems/c8fd93ee-4559-4e83-933b-9a8d0fac5b2f
-- title:
--   Heisenberg Gaussian Series: summable coeff
-- statement:
--   The Heisenberg Gaussian Series construction uses the summable coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L49-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L49-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries

theorem GlobalTheory.HeisenbergGaussianSeries.summable_coeff {G V : Type} [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : G →+ V) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ U₀ : AddSubgroup G) (χ : G → ℂ) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0)
    (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1)
    (b : Γ → ℂ) (hb : ∀ g, ‖b g‖ = 1) (w : G) (y : V) (M : V →L[ℝ] V →L[ℝ] ℂ) (R : ℝ) :
    Summable fun g : Γ => ‖b g * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))‖ *
        Real.exp (R * ‖M (p g + y)‖) := by sorry
