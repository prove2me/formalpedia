-- Prove2me | Theorems.Thm_MellinDuality_coset_trace_second
-- name    : MellinDuality.coset_trace_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:01:29.331816+00:00
-- url     : https://prove2.me/theorems/ff70e92b-14fa-563d-96ff-2dff25e08343
-- title:
--   Mellin Duality: coset trace second
-- statement:
--   **The coset trace, second form** (Corollary 3.3): `2 ∑_{χ(a) = c} 𝒞(a) = c̄ |γ|² + c γ̄²`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L138-L142
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L138-L142

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.coset_trace_second {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 := by sorry
