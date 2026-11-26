-- Prove2me | Theorems.Thm_MellinDuality_char_neg_one_sq
-- name    : MellinDuality.char_neg_one_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:07.877964+00:00
-- url     : https://prove2.me/theorems/8df7ed0f-eaad-5216-9471-41b06e7bb197
-- title:
--   Mellin Duality: char neg one sq
-- statement:
--   The Mellin Duality construction uses the char neg one sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L36-L37
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L36-L37

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.char_neg_one_sq (ψ : DirichletCharacter ℂ p) : ψ (-1) * ψ (-1) = 1 := by sorry
