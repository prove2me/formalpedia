-- Prove2me | Theorems.Thm_MellinDuality_apply_neg_of_odd
-- name    : MellinDuality.apply_neg_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:48.471248+00:00
-- url     : https://prove2.me/theorems/27a4b463-65b9-5cdd-98c6-6f78848e413e
-- title:
--   Mellin Duality: apply neg of odd
-- statement:
--   The Mellin Duality construction uses the apply neg of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L85-L87
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L85-L87

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem MellinDuality.apply_neg_of_odd (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) (x : ZMod p) :
    φ (-x) = -φ x := by sorry
