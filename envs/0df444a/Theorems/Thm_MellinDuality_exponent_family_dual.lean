-- Prove2me | Theorems.Thm_MellinDuality_exponent_family_dual
-- name    : MellinDuality.exponent_family_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:35.510017+00:00
-- url     : https://prove2.me/theorems/59898b15-1cfb-598d-ac14-31430a2fe29d
-- title:
--   Mellin Duality: exponent family dual
-- statement:
--   **The exponent family** (Corollary 3.2): for `m ≥ 1`,
--   `𝒞_{2m} = (1/(2(p-1))) ∑_{ψ odd} 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L85-L89
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L85-L89

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.exponent_family_dual (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
