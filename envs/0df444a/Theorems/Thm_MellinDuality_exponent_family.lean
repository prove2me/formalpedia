-- Prove2me | Theorems.Thm_MellinDuality_exponent_family
-- name    : MellinDuality.exponent_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:42.926487+00:00
-- url     : https://prove2.me/theorems/f0d697d8-73a4-4e61-8ae5-0421529f354e
-- title:
--   Mellin Duality: exponent family
-- statement:
--   **The exponent family** (Corollary 3.2 of Paper II): for `m ≥ 1`,
--   `𝒞_{2m} = (1/(2(p-1))) ∑_{ψ odd} 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L288-L293
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L288-L293

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.exponent_family (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) {m : ℕ}
    (hm : 1 ≤ m) :
    bandSumPow χ (2 * m) = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
