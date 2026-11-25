-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_ringEquiv
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.of_ringEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:40.835567+00:00
-- url     : https://prove2.me/theorems/4393d482-a144-4654-9c31-06c1df72cc0b
-- title:
--   Is Perfectoid Field: of ring Equiv
-- statement:
--   The Is Perfectoid Field construction uses the of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L188-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean#L188-L211

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.of_ringEquiv {F F' : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField F'] [IsUltrametricDist F'] (p : ℕ) [Fact p.Prime]
    [IsPerfectoidField F p] (e : F ≃+* F') (he : ∀ x, ‖e x‖ = ‖x‖) : IsPerfectoidField F' p := by sorry
