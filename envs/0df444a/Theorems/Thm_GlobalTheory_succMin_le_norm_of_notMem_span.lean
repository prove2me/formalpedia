-- Prove2me | Theorems.Thm_GlobalTheory_succMin_le_norm_of_notMem_span
-- name    : GlobalTheory.succMin_le_norm_of_notMem_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:08.511941+00:00
-- url     : https://prove2.me/theorems/d6ffca91-01f5-47b9-b835-5549eecb35d0
-- title:
--   Global Theory: succ Min le norm of not Mem span
-- statement:
--   The Global Theory construction uses the succ Min le norm of not Mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsLinearIndependentSqrtEqSuccMinQuad.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsLinearIndependentSqrtEqSuccMinQuad.lean#L95-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}

theorem GlobalTheory.succMin_le_norm_of_notMem_span {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ := by sorry
