-- Prove2me | Theorems.Thm_MellinDuality_pair_structure_identities
-- name    : MellinDuality.pair_structure_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:01:59.220276+00:00
-- url     : https://prove2.me/theorems/ed11d0a8-cf19-518e-a829-a4b68b8fc48d
-- title:
--   Mellin Duality: pair structure identities
-- statement:
--   **The pair structure** (Proposition 6.3): `𝒞 S̄`, `𝒞 S`, `|𝒞|²` and `𝒞²` as sums over coprime
--   pairs `(a, b)` of inner sums over `r ≤ ⌊N / max(a, b)⌋`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L180-L196
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L180-L196

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.pair_structure_identities {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) (hp8 : p % 8 = 5) :
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
