-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_series_neg
-- name    : GlobalTheory.HeisenbergGaussianSeries.series_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:07.909937+00:00
-- url     : https://prove2.me/theorems/47acc86a-fbdf-4d43-83ba-ad35eb4745c6
-- title:
--   Heisenberg Gaussian Series: series neg
-- statement:
--   The Heisenberg Gaussian Series construction uses the series neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L160-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L160-L181

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

theorem GlobalTheory.HeisenbergGaussianSeries.series_neg (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (halt : ∀ v, om v v = 0) (hχ : ∀ x v, χ (x + ι v) = χ x) (a : V) :
    series p ι β om J Γ χ a (ι (-a)) =
      ∑' g : Γ, (χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) *
        Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) := by sorry
