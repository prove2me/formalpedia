-- Prove2me | Theorems.Thm_MellinDuality_mellin_inversion
-- name    : MellinDuality.mellin_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:59.248025+00:00
-- url     : https://prove2.me/theorems/55fb322b-50cb-5253-8f07-89bacf515796
-- title:
--   Mellin Duality: mellin inversion
-- statement:
--   **Mellin duality, inverted** (Theorem 3.1 of Paper II, for the exponent `2m`). For an odd
--   prime `p`, an odd complex character `χ` and a unit `a`,
--   `𝒞_χ^{(2m)}(a) = (1/(2(p - 1))) ∑_{ψ odd} ψ(a) 𝒢(ψ̄) 𝒢(χ ψ^{2m})`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L219-L248
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L219-L248

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mellin_inversion (hp2 : p ≠ 2) (χ : DirichletCharacter ℂ p) (hχ : χ (-1) = -1) (m : ℕ)
    {a : ZMod p} (ha : a ≠ 0) :
    fam χ (2 * m) a = 1 / (2 * ((p : ℂ) - 1)) *
      ∑ ψ ∈ oddChars p, ψ a * G ψ⁻¹ * G (χ * ψ ^ (2 * m)) := by sorry
