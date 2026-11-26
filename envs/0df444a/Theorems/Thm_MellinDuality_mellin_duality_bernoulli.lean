-- Prove2me | Theorems.Thm_MellinDuality_mellin_duality_bernoulli
-- name    : MellinDuality.mellin_duality_bernoulli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:20.212371+00:00
-- url     : https://prove2.me/theorems/7eaa2bf2-841a-4ec7-9d19-77c7f3cb3872
-- title:
--   Mellin Duality: mellin duality bernoulli
-- statement:
--   **Mellin duality in Bernoulli form** (Theorem 3.1): `𝒞_χ(a) = (2/(p-1)) ∑_{ψ odd} ψ(a)
--   (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L63-L67
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L63-L67

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_duality_bernoulli (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ 2 a = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by sorry
