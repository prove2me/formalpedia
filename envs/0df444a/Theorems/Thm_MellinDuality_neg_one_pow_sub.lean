-- Prove2me | Theorems.Thm_MellinDuality_neg_one_pow_sub
-- name    : MellinDuality.neg_one_pow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:10.788637+00:00
-- url     : https://prove2.me/theorems/66e4475d-4744-5359-af4e-8726c5307ffa
-- title:
--   Mellin Duality: neg one pow sub
-- statement:
--   The Mellin Duality construction uses the neg one pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L33-L39
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L33-L39

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.neg_one_pow_sub (hp2 : p ≠ 2) {v : ℕ} (hv : v ≤ p) :
    (-1 : ℤ) ^ (p - v) = -(-1) ^ v := by sorry
