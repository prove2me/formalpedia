-- Prove2me | Theorems.Thm_MellinDuality_multiplier_constant_half
-- name    : MellinDuality.multiplier_constant_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:22.656023+00:00
-- url     : https://prove2.me/theorems/50034a13-28fb-5cf5-a204-09e05e220345
-- title:
--   Mellin Duality: multiplier constant half
-- statement:
--   **The half sums** (Paper II, §2). For an odd character `φ`, `𝒢(φ) = 2 ∑_{0<n<p/2} φ(n)(-1)^n` and
--   `𝒢(φ) = 2 φ(2) ∑_{0<m<p/2} φ(m)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L26-L28
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L26-L28

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.multiplier_constant_half {R : Type*} [CommRing R] (hp2 : p ≠ 2) (φ : MulChar (ZMod p) R) (hφ : φ (-1) = -1) :
    G φ = 2 * ∑ n ∈ half p, φ n * (parSign n : R) ∧ G φ = 2 * φ 2 * ∑ n ∈ half p, φ n := by sorry
