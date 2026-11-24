-- Prove2me | Theorems.Thm_GlobalTheory_exists_root_near_of_norm_eval_lt
-- name    : GlobalTheory.exists_root_near_of_norm_eval_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:17.08987+00:00
-- url     : https://prove2.me/theorems/df54a551-c259-41b2-9b62-a3884eb49ab1
-- title:
--   Global Theory: exists root near of norm eval lt
-- statement:
--   The Global Theory construction uses the exists root near of norm eval lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEmbeddingsOverInjective.lean#L72-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEmbeddingsOverInjective.lean#L72-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_root_near_of_norm_eval_lt (p : Polynomial ℂ) (hp : p.Monic) (x : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ‖p.eval x‖ < δ ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖r - x‖ < δ := by sorry
