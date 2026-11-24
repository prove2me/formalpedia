-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_norm_sub_pow_le
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.of_norm_sub_pow_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:20.129478+00:00
-- url     : https://prove2.me/theorems/48412dd3-31cf-4d4a-a84b-1475fe7d8693
-- title:
--   Is Perfectoid Field: of norm sub pow le
-- statement:
--   The Is Perfectoid Field construction uses the of norm sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L108-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L108-L186

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.of_norm_sub_pow_le {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (hnd : ∀ r : ℝ, r < 1 → ∃ x : F, r < ‖x‖ ∧ ‖x‖ < 1) {π : F} (hπ : ‖π‖ < 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p) : IsPerfectoidField F p := by sorry
