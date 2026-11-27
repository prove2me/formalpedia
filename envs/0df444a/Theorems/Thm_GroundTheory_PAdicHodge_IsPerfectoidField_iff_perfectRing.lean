-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_iff_perfectRing
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.iff_perfectRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:37.03189+00:00
-- url     : https://prove2.me/theorems/c9bd3cb1-5a4a-5c6b-8318-e545371ab01d
-- title:
--   Is Perfectoid Field: iff perfect Ring
-- statement:
--   The Is Perfectoid Field construction uses the iff perfect Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L240-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L240-L243

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.iff_perfectRing (p : ℕ) [Fact p.Prime] [CharP K p] [CompleteSpace K]
    (h : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1) :
    IsPerfectoidField K p ↔ PerfectRing K p := by sorry
