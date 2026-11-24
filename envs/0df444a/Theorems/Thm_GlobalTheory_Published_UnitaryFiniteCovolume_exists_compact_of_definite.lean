-- Prove2me | Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_exists_compact_of_definite
-- name    : GlobalTheory.Published.UnitaryFiniteCovolume.exists_compact_of_definite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:44.674955+00:00
-- url     : https://prove2.me/theorems/3cbb8df7-a000-49b5-84ed-7a7899abdf60
-- title:
--   Unitary Finite Covolume: exists compact of definite
-- statement:
--   The Unitary Finite Covolume construction uses the exists compact of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L25-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/DefiniteCompactness/ExistsCompactOfDefinite.lean#L25-L66

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

theorem GlobalTheory.Published.UnitaryFiniteCovolume.exists_compact_of_definite {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r) (τ : X.Ψ) :
    ∃ K : Set (Matrix (Fin r) (Fin r) ℂ), IsCompact K ∧ ∀ g : Matrix (Fin r) (Fin r) ℂ,
      (∀ u w, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ w) = hermC τ.1 X.Gm u w) → g ∈ K := by sorry
