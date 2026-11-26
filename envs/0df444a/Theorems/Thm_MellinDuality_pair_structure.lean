-- Prove2me | Theorems.Thm_MellinDuality_pair_structure
-- name    : MellinDuality.pair_structure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:58.170808+00:00
-- url     : https://prove2.me/theorems/402865a6-579f-4b0a-9d66-b9ec11a8a1dc
-- title:
--   Mellin Duality: pair structure
-- statement:
--   **The pair structure** (Proposition 6.3 of Paper II). For `p ≡ 5 (mod 8)` and a quartic
--   `χ`, with `N = (p - 1)/2`, `𝒞 = bandSumPow χ 2`, `S = halfSum χ`, the outer sums over coprime
--   `a, b ≤ N` and the inner sums over `r ≤ ⌊N / max(a, b)⌋`:
--   `𝒞 S̄ = ∑ χ(a) χ̄(b) ∑ ε_{ar}`, `𝒞 S = ∑ χ(ab) ∑ (r/p) ε_{ar}`,
--   `𝒞 𝒞̄ = ∑ χ(a) χ̄(b) ∑ ε_{ar} ε_{br}` and `𝒞² = ∑ χ(ab) ∑ (r/p) ε_{ar} ε_{br}`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L125-L180
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L125-L180

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem MellinDuality.pair_structure (hp8 : p % 8 = 5) :
    bandSumPow χ 2 * star (halfSum χ) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * halfSum χ =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            ((legendreSym p r : ℤ) : GaussianInt) * (eps p (ab.1 * r) : GaussianInt) ∧
      bandSumPow χ 2 * star (bandSumPow χ 2) =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ ab.1 * star (χ ab.2) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab,
            (eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt) ∧
      bandSumPow χ 2 * bandSumPow χ 2 =
        ∑ ab ∈ coprimePairs ((p - 1) / 2), χ (ab.1 * ab.2 : ℕ) *
          ∑ r ∈ pairRange ((p - 1) / 2) ab, ((legendreSym p r : ℤ) : GaussianInt) *
            ((eps p (ab.1 * r) : GaussianInt) * (eps p (ab.2 * r) : GaussianInt)) := by sorry
