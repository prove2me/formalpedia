-- Prove2me | Theorems.Thm_MellinDuality_pow_apply_of_ne_zero
-- name    : MellinDuality.pow_apply_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:53.33055+00:00
-- url     : https://prove2.me/theorems/c1e4025e-267d-56b0-aa96-3e8332bb9cdf
-- title:
--   Mellin Duality: pow apply of ne zero
-- statement:
--   The Mellin Duality construction uses the pow apply of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L34-L36
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L34-L36

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

theorem MellinDuality.pow_apply_of_ne_zero (ψ : MulChar (ZMod p) R) (k : ℕ) {x : ZMod p} (hx : x ≠ 0) :
    (ψ ^ k) x = ψ x ^ k := by sorry
