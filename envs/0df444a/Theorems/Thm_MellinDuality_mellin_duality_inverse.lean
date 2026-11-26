-- Prove2me | Theorems.Thm_MellinDuality_mellin_duality_inverse
-- name    : MellinDuality.mellin_duality_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:06.562813+00:00
-- url     : https://prove2.me/theorems/ef95af3b-d50d-4e76-a174-fe21950cc887
-- title:
--   Mellin Duality: mellin duality inverse
-- statement:
--   **Mellin duality, inverted** (Theorem 3.1). For an odd complex character `χ` and a unit `a`,
--   `𝒞_χ^{(2m)}(a) = (1/(2(p-1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L55-L59
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L55-L59

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_duality_inverse (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
