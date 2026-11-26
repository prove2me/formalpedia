-- Prove2me | Theorems.Thm_MellinDuality_mellin_bernoulli
-- name    : MellinDuality.mellin_bernoulli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:46:08.287579+00:00
-- url     : https://prove2.me/theorems/dddfa7e1-82a8-5b78-829b-5eb22628f2a5
-- title:
--   Mellin Duality: mellin bernoulli
-- statement:
--   **Mellin duality in Bernoulli form** (Theorem 3.1 of Paper II): for an odd complex character
--   `χ` and a unit `a`,
--   `𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L262-L274
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L262-L274

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_bernoulli (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by sorry
