-- Prove2me | Theorems.Thm_MellinDuality_mellin_quartic
-- name    : MellinDuality.mellin_quartic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:32.961704+00:00
-- url     : https://prove2.me/theorems/9172db3d-64ee-43c2-ae5b-60e50ce21b2c
-- title:
--   Mellin Duality: mellin quartic
-- statement:
--   **The quartic case** (Theorem 3.1 of Paper II, last display): for an odd complex character
--   with `χ(2) = i` (the quartic character at `p ≡ 5 (mod 8)`),
--   `𝒞 = (2/(p-1)) ∑_{ψ odd} (1 - 2ψ̄(2)) (1 - 2iψ(2)²) B_{1,ψ̄} B_{1,χψ²}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L279-L284
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L279-L284

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_quartic (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1)
    (hpin : χ 2 = Complex.I) :
    bandSumPow χ 2 = 2 / ((p : ℂ) - 1) * ∑ ψ ∈ oddChars p, (1 - 2 * ψ⁻¹ 2) *
      (1 - 2 * Complex.I * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2) := by sorry
