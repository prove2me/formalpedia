-- Prove2me | Theorems.Thm_GlobalTheory_PositiveLowerBoundFinset_pos_lower_bound_on_finset
-- name    : GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:52.418823+00:00
-- url     : https://prove2.me/theorems/3bd7bad8-423f-450c-bb9c-3230837fb26a
-- title:
--   Positive Lower Bound Finset: pos lower bound on finset
-- statement:
--   The Positive Lower Bound Finset construction uses the pos lower bound on finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosLowerBoundOnFinset.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosLowerBoundOnFinset.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosLowerBoundOnFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PositiveLowerBoundFinset

theorem GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by sorry
