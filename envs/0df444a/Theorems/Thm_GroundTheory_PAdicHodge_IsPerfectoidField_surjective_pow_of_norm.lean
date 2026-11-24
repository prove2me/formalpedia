-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_pow_of_norm
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.surjective_pow_of_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:31.445635+00:00
-- url     : https://prove2.me/theorems/f04191b1-3847-48d9-8bab-6ded3db5a1c7
-- title:
--   Is Perfectoid Field: surjective pow of norm
-- statement:
--   The Is Perfectoid Field construction uses the surjective pow of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L15-L31

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
variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.surjective_pow_of_norm
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖) :
    Function.Surjective (fun x : ModP (normInteger F) p => x ^ p) := by sorry
