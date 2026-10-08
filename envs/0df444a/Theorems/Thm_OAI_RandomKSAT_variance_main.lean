-- Prove2me | Theorems.Thm_OAI_RandomKSAT_variance_main
-- name    : OAI.RandomKSAT.variance_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.745341+00:00
-- url     : https://prove2.me/theorems/e0ea3857-7ab1-4da5-9ecf-b3188a7c5f16
-- statement:
--   The theorem states that, for every integer k ≥ 3, three assertions hold about random k-SAT clause streams. A clause on n variables is a choice of k distinct variables together with a Boolean sign for each; an assignment satisfies it if it agrees with the clause's sign on at least one of its variables. A stream is an infinite sequence of independent clauses, each drawn uniformly from all such clauses (the product law streamLaw n k). The first failure time of a stream is the least m such that the first m clauses have no common satisfying assignment (infinite if none exists). H is this first-failure time converted to a real number, with an infinite value read as 0, and T B is the first-failure time truncated at cap ⌊B n⌋, likewise converted to a real number. Let ell(k,n) be log(e n) when k = 3 and 1 otherwise, and let U(k) = log 2 / (−log(1 − 2^(−k))). First, there is a constant C ≥ 0 such that for all n ≥ k the variance of H under streamLaw n k is at most C n ell(k,n). Second, for every B > 0 there is a constant C ≥ 0 (depending on B) such that for all n ≥ k the variance of T B is at most C n ell(k,n). Third, there is a constant c > 0 such that, for all sufficiently large n, the variance of H is at least c n, and for every B > U(k), for all sufficiently large n, the variance of T B is also at least c n; the threshold in n may depend on B, while c does not. The proof is admitted, not verified.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SATVariance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SATVariance.lean; bytes 1524..2195
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SATVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

theorem variance_main (k : ℕ) (hk : 3 ≤ k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k))) := by
  sorry

end RandomKSAT
end
end OAI
