-- Prove2me | Theorems.Thm_MellinDuality_coset_trace_values
-- name    : MellinDuality.coset_trace_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:06.435671+00:00
-- url     : https://prove2.me/theorems/9dc615c6-9475-4654-a118-ac84528c5fb5
-- title:
--   Mellin Duality: coset trace values
-- statement:
--   **The coset trace** (Corollary 3.3): for `c ∈ {1, i, -1, -i}`,
--   `∑_{χ(a) = c} 𝒞(a) = Re(c̄ γ) γ̄`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L132-L135
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L132-L135

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.coset_trace_values {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    ∑ a ∈ fiber χ c, fam χ 2 a = ((star c * gamma χ).re : GaussianInt) * star (gamma χ) := by sorry
