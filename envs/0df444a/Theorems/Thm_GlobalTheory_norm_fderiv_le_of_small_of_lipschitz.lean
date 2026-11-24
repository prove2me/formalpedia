-- Prove2me | Theorems.Thm_GlobalTheory_norm_fderiv_le_of_small_of_lipschitz
-- name    : GlobalTheory.norm_fderiv_le_of_small_of_lipschitz
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:52.586206+00:00
-- url     : https://prove2.me/theorems/1f833af9-c86f-4710-88a5-b5c007eb5756
-- title:
--   Global Theory: norm fderiv le of small of lipschitz
-- statement:
--   The Global Theory construction uses the norm fderiv le of small of lipschitz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L7-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L7-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.norm_fderiv_le_of_small_of_lipschitz {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} (hg : Differentiable ℝ g) {C δ t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hL : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ C * ‖a - b‖) (hδ : ∀ w, ‖g w‖ ≤ δ) (v : V) :
    ‖fderiv ℝ g v‖ ≤ 2 * δ / t + C * t := by sorry
