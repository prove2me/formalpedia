-- Prove2me | Theorems.Thm_MellinDuality_sum_fiber_fam
-- name    : MellinDuality.sum_fiber_fam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:19.619632+00:00
-- url     : https://prove2.me/theorems/d28a58ca-50d6-5cba-912a-59e9f04d488b
-- title:
--   Mellin Duality: sum fiber fam
-- statement:
--   `∑_{a ∈ cH} 𝒞(a) = σ(c) γ̄`, with the coset as a fibre.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L186-L212
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L186-L212

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
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ

theorem MellinDuality.sum_fiber_fam {c : GaussianInt} (hc0 : c ≠ 0) :
    ∑ a ∈ fiber χ c, fam χ 2 a = (sigma χ c : GaussianInt) * star (gamma χ) := by sorry
