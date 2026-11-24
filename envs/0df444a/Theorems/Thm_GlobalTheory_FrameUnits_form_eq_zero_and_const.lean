-- Prove2me | Theorems.Thm_GlobalTheory_FrameUnits_form_eq_zero_and_const
-- name    : GlobalTheory.FrameUnits.form_eq_zero_and_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:24.61962+00:00
-- url     : https://prove2.me/theorems/2bc47a09-4ce0-415b-8cc0-57ac6439ae47
-- title:
--   Frame Units: form eq zero and const
-- statement:
--   The Frame Units construction uses the form eq zero and const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L49-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L49-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem GlobalTheory.FrameUnits.form_eq_zero_and_const {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (ψ : E → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : E → E → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = star (D z w))
    (hper : ∀ l ∈ S, ∃ ρ : ℂ, ‖ρ‖ = 1 ∧ ∀ z, ψ (z + l) = ρ * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ z, ψ z = ψ 0 := by sorry
