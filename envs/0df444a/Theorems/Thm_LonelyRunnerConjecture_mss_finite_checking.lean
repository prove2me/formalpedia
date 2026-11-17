-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_mss_finite_checking
-- name    : LonelyRunnerConjecture.mss_finite_checking
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T01:14:16.044319+00:00
-- url     : https://prove2.me/theorems/954bf6ca-1c2c-4fe8-9ece-8d90193ba02a
-- title:
--   Malikiosis–Santos–Schymura finite checking
-- statement:
--   Assume the conjecture for $n$ runners ($\mathrm{LRC}(n-1)$). Then it holds for $n+1$ runners with positive integer speeds $v_1,\dots,v_n$ satisfying $\gcd(v_1,\dots,v_n)=1$ and $\sum_{S\subseteq[n]} v_S > \binom{n+1}{2}^{n-1}$, where $v_S=\gcd(v_i:i\in S)$. This linearly-exponential bound underlies the recent small-case proofs.
--
--   **Formalization Note** The sum runs over `Finset.univ.powerset` with `Finset.gcd ∅ = 0`; the bound is `Nat.choose (n+1) 2 ^ (n-1)`. Speeds need not be distinct.
-- source:
--   R. D. Malikiosis, F. Santos, M. Schymura, Linearly-exponential checking is enough for the LRC, https://arxiv.org/abs/2411.06903, Theorem A.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs
open scoped BigOperators

namespace LonelyRunnerConjecture

theorem mss_finite_checking (n : ℕ) (hn : 1 ≤ n) (h : LRC (n - 1))
    (v : Fin n → ℕ) (hpos : ∀ i, 0 < v i)
    (hgcd : Finset.gcd Finset.univ v = 1)
    (hsum : (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) > Nat.choose (n + 1) 2 ^ (n - 1)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤ distToNearestInt (t * (v i : ℝ)) := by sorry

end LonelyRunnerConjecture
