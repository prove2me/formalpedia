-- Prove2me | Theorems.Thm_GlobalTheory_exists_forall_eval_add_ne_zero
-- name    : GlobalTheory.exists_forall_eval_add_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:35.201218+00:00
-- url     : https://prove2.me/theorems/83ca50b5-66f4-44a8-a9ad-12ac1306f208
-- title:
--   Global Theory: exists forall eval add ne zero
-- statement:
--   The Global Theory construction uses the exists forall eval add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/InfinitePowCharEqOneOfAdditiveFamily.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/InfinitePowCharEqOneOfAdditiveFamily.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_InfinitePowCharEqOneOfAdditiveFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_forall_eval_add_ne_zero {k : Type} [Field k] [Infinite k] {Q : Polynomial k}
    (hQ : Q ≠ 0) (S : Finset k) : ∃ β : k, ∀ c ∈ S, Q.eval (c + β) ≠ 0 := by sorry
