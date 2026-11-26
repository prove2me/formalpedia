-- Prove2me | Theorems.Thm_MellinDuality_ne_zero_of_mem_fiber
-- name    : MellinDuality.ne_zero_of_mem_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:58.556229+00:00
-- url     : https://prove2.me/theorems/0eb4891c-58a6-524e-9172-9c3b17dc64d1
-- title:
--   Mellin Duality: ne zero of mem fiber
-- statement:
--   The Mellin Duality construction uses the ne zero of mem fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L53-L55
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L53-L55

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}

theorem MellinDuality.ne_zero_of_mem_fiber {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by sorry
