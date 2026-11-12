-- Prove2me | Theorems.Thm_OAIJacobsthal_exists_jacobsthal_bound_le_sq_div_loglog_sq
-- name    : OAIJacobsthal.exists_jacobsthal_bound_le_sq_div_loglog_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:33:33.553106+00:00
-- url     : https://prove2.me/theorems/ae54e8e8-bb09-4cd9-834b-97bd419637a6
-- title:
--   Jacobsthal's function is at most a constant times k² / (log log 3k)²
-- statement:
--   There is a constant $C > 0$ such that for every integer $k \ge 1$ there is a natural number $m$ with
--   $$m \le \frac{C\,k^2}{(\log\log 3k)^2}$$
--   such that for every positive integer $n$ with at most $k$ distinct prime factors and every integer $a$, one of the $m$ consecutive integers $a, a+1, \dots, a+m-1$ is coprime to $n$ (that is, $m$ bounds Jacobsthal's function $j(n)$ uniformly over all $n$ with at most $k$ prime factors).
--
--   This is the statement of OpenAI's `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log` (OpenAI, *A quadratic bound for Jacobsthal's function*, OpenAI Math Release, September 25, 2026), written without that statement's definitions bundle. The two OpenAI goals about Jacobsthal's function ship definitions bundles that both declare `IsJacobsthalBound`, so a proof cannot import both; this statement, which imports no bundle, lets the weaker quadratic bound follow from the stronger one.
-- source:
--   The statement of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log` of OpenAI, "A quadratic bound for Jacobsthal's function" (OpenAI Math Release, September 25, 2026, result family 21, https://github.com/openai/math), with the definitions unfolded.

import Mathlib

namespace OAIJacobsthal

theorem exists_jacobsthal_bound_le_sq_div_loglog_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ,
        (∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
          ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n) ∧
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 := by
  sorry

end OAIJacobsthal
