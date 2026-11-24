-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_expand
-- name    : GlobalTheory.HeisenbergGaussianSeries.series_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:07.696799+00:00
-- url     : https://prove2.me/theorems/8b0fb808-92e8-4be6-a6d5-ccd6e47a5942
-- title:
--   Heisenberg Gaussian Series: series expand
-- statement:
--   The Heisenberg Gaussian Series construction uses the series expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L125-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L125-L158

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
variable {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}

theorem GlobalTheory.HeisenbergGaussianSeries.series_expand (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hsym : ∀ x y, om x (J y) = om y (J x)) (hχ : ∀ x v, χ (x + ι v) = χ x)
    (M : V → V → ℂ)
    (hM : ∀ y v, M y v = -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (a : V) (w : G) (v : V) :
    β w (ι v) * series p ι β om J Γ χ a (w + ι v) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      ∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
        Complex.exp (M (p g + (a + p w)) v) := by sorry
