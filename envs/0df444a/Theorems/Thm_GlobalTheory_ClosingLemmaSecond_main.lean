-- Prove2me | Theorems.Thm_GlobalTheory_ClosingLemmaSecond_main
-- name    : GlobalTheory.ClosingLemmaSecond.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:47.562138+00:00
-- url     : https://prove2.me/theorems/0383d410-e244-486c-bdf0-e96d502b74b1
-- title:
--   Closing Lemma Second: main
-- statement:
--   The Closing Lemma Second construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsExtraMore.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsExtraMore.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosingLemmaSecond

theorem GlobalTheory.ClosingLemmaSecond.main : ∀ {R : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R}, q ≠ (0 : R) → ∃ (c : ℕ), ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by sorry
