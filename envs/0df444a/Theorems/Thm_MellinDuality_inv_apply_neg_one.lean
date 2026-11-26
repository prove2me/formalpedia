-- Prove2me | Theorems.Thm_MellinDuality_inv_apply_neg_one
-- name    : MellinDuality.inv_apply_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:36.119335+00:00
-- url     : https://prove2.me/theorems/23189498-00be-5984-8a22-876f7a4bf7f9
-- title:
--   Mellin Duality: inv apply neg one
-- statement:
--   The Mellin Duality construction uses the inv apply neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L50-L51
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L50-L51

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.inv_apply_neg_one (ψ : MulChar (ZMod p) R) : ψ⁻¹ (-1) = ψ (-1) := by sorry
