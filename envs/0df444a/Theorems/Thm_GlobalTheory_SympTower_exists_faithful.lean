-- Prove2me | Theorems.Thm_GlobalTheory_SympTower_exists_faithful
-- name    : GlobalTheory.SympTower.exists_faithful
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:34.309213+00:00
-- url     : https://prove2.me/theorems/650cf804-c86a-48dd-8152-8e098c722f8a
-- title:
--   Symp Tower: exists faithful
-- statement:
--   The Symp Tower construction uses the exists faithful property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L57-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower

theorem GlobalTheory.SympTower.exists_faithful {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    [Finite V] (h : ∀ c : ZMod n, (∀ y : V, c • y = 0) → c = 0) :
    ∃ x : V, ∀ c : ZMod n, c • x = 0 → c = 0 := by sorry
