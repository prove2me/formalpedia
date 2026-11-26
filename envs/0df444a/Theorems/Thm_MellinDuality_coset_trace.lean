-- Prove2me | Theorems.Thm_MellinDuality_coset_trace
-- name    : MellinDuality.coset_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:17.145159+00:00
-- url     : https://prove2.me/theorems/3e70e5b5-9fd8-5f82-8993-2cd367abb164
-- title:
--   Mellin Duality: coset trace
-- statement:
--   **The coset trace** (Corollary 3.3 of Paper II). For `c ∈ {1, i, -1, -i}`, the sum of the
--   family over the fibre `{a : χ(a) = c}` (the coset `gH` with `χ(g) = c`) is `Re(c̄ γ) γ̄`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L216-L219
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L216-L219

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

theorem MellinDuality.coset_trace {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) := by sorry
