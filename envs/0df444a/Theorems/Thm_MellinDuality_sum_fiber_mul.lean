-- Prove2me | Theorems.Thm_MellinDuality_sum_fiber_mul
-- name    : MellinDuality.sum_fiber_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:16.167851+00:00
-- url     : https://prove2.me/theorems/8d94a8bb-6c06-5c3b-a9ad-ad8c9fb6eec4
-- title:
--   Mellin Duality: sum fiber mul
-- statement:
--   Multiplying by `w ≠ 0` maps the fibre of `c` onto the fibre of `c χ(w)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L58-L68
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L58-L68

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

theorem MellinDuality.sum_fiber_mul {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (c : GaussianInt)
    {w : ZMod p} (hw : w ≠ 0) (hwu : χ w * χ w⁻¹ = 1) :
    ∑ a ∈ fiber χ c, f (a * w) = ∑ b ∈ fiber χ (c * χ w), f b := by sorry
