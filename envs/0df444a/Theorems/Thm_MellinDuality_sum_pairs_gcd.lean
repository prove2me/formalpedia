-- Prove2me | Theorems.Thm_MellinDuality_sum_pairs_gcd
-- name    : MellinDuality.sum_pairs_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:26.875704+00:00
-- url     : https://prove2.me/theorems/3a7d40c9-2c1a-57f0-b5d7-fac4364b55ad
-- title:
--   Mellin Duality: sum pairs gcd
-- statement:
--   **The gcd decomposition.** `∑_{n, n' ≤ N} F(n, n') = ∑_{(a,b) coprime} ∑_{r ≤ K(a,b)} F(ar, br)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L29-L76
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L29-L76

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset

theorem MellinDuality.sum_pairs_gcd {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) := by sorry
