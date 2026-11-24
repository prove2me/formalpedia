-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_norm_sub_pow_le
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_norm_sub_pow_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:45.488863+00:00
-- url     : https://prove2.me/theorems/38148cb8-5a02-4a03-bf75-ec551696c6b9
-- title:
--   Is Perfectoid Field: exists norm sub pow le
-- statement:
--   The Is Perfectoid Field construction uses the exists norm sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L43-L56

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_norm_sub_pow_le [IsPerfectoidField F p] {x : F} (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by sorry
