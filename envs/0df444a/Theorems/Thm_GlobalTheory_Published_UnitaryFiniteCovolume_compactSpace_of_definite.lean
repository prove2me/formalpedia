-- Prove2me | Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_compactSpace_of_definite
-- name    : GlobalTheory.Published.UnitaryFiniteCovolume.compactSpace_of_definite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:00.110695+00:00
-- url     : https://prove2.me/theorems/f05e0a18-de7d-4405-a90b-9e4ef91d1fb6
-- title:
--   Unitary Finite Covolume: compact Space of definite
-- statement:
--   The Unitary Finite Covolume construction uses the compact Space of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L68-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.Published.UnitaryFiniteCovolume.compactSpace_of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) :
    CompactSpace H := by sorry
