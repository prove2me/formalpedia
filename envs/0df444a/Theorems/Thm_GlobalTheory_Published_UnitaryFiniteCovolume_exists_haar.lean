-- Prove2me | Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_exists_haar
-- name    : GlobalTheory.Published.UnitaryFiniteCovolume.exists_haar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:28.035658+00:00
-- url     : https://prove2.me/theorems/787d258c-834b-4cbc-980c-ce3e4e230a76
-- title:
--   Unitary Finite Covolume: exists haar
-- statement:
--   The Unitary Finite Covolume construction uses the exists haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L98-L106

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

theorem GlobalTheory.Published.UnitaryFiniteCovolume.exists_haar {r : ℕ} (X : Data E r) :
    ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧
      ∃ (_ : MeasurableSpace H) (_ : BorelSpace H) (ν : Measure H), ν.IsHaarMeasure := by sorry
