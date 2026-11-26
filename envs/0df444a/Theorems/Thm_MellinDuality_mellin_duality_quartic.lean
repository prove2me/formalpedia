-- Prove2me | Theorems.Thm_MellinDuality_mellin_duality_quartic
-- name    : MellinDuality.mellin_duality_quartic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:29.435677+00:00
-- url     : https://prove2.me/theorems/c4da9e54-fd6d-42c4-b7b7-6da098c163df
-- title:
--   Mellin Duality: mellin duality quartic
-- statement:
--   **The quartic case** (Theorem 3.1, last display): if `χ` is odd with `χ(2) = i`,
--   `𝒞 = (2/(p-1)) ∑_{ψ odd} (1 - 2ψ̄(2)) (1 - 2iψ(2)²) B_{1,ψ̄} B_{1,χψ²}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L71-L75
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L71-L75

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_duality_quartic (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by sorry
