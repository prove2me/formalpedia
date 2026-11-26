-- Prove2me | Theorems.Thm_MellinDuality_coset_trace_second_form
-- name    : MellinDuality.coset_trace_second_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:46.890868+00:00
-- url     : https://prove2.me/theorems/08f28547-58df-5540-8e3b-6b90a3849cfb
-- title:
--   Mellin Duality: coset trace second form
-- statement:
--   **The coset trace, second form**: `2 ∑_{a ∈ cH} 𝒞(a) = c̄ |γ|² + c γ̄²`; with `γ = (1 - 2i)β`
--   this is `5|β|² c̄ + γ̄² c`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L223-L230
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L223-L230

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

theorem MellinDuality.coset_trace_second_form {c : GaussianInt} (hc : c = 1 ∨ c = gi ∨ c = -1 ∨ c = -gi) :
    2 * ∑ a ∈ fiber χ c, fam χ 2 a =
      star c * (gamma χ * star (gamma χ)) + c * star (gamma χ) ^ 2 := by sorry
