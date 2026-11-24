-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_perfectRing
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.of_perfectRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:04.63613+00:00
-- url     : https://prove2.me/theorems/108c9137-4325-4052-b276-6ffe812a3354
-- title:
--   Is Perfectoid Field: of perfect Ring
-- statement:
--   The Is Perfectoid Field construction uses the of perfect Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L206-L212

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
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
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.of_perfectRing (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p] [CompleteSpace K]
    (h : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1) : IsPerfectoidField K p := by sorry
