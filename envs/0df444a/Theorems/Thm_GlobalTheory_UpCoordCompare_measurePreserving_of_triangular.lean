-- Prove2me | Theorems.Thm_GlobalTheory_UpCoordCompare_measurePreserving_of_triangular
-- name    : GlobalTheory.UpCoordCompare.measurePreserving_of_triangular
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:28:03.658851+00:00
-- url     : https://prove2.me/theorems/aa6fe8e3-5d4d-4420-9bfa-00bcf110891d
-- title:
--   Up Coord Compare: measure Preserving of triangular
-- statement:
--   The Up Coord Compare construction uses the measure Preserving of triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeadingBlockLowerEntriesToBlockCoords.lean#L22-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeadingBlockLowerEntriesToBlockCoords.lean#L22-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeadingBlockLowerEntriesToBlockCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpCoordCompare
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff
noncomputable section

theorem GlobalTheory.UpCoordCompare.measurePreserving_of_triangular {n : ℕ} (F : V n → V n) (hF : Differentiable ℝ F)
    (hb : Function.Bijective F) (ρ : Fin n → ℕ)
    (htri : ∀ (i : Fin n) (z w : V n), (∀ j, ρ j < ρ i → z j = w j) → F z i - z i = F w i - w i) :
    MeasurePreserving F volume volume := by sorry
