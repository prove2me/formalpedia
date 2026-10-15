-- Prove2me | Theorems.Thm_JRPHard_Periodic_exists_small_divisor
-- name    : JRPHard.Periodic.exists_small_divisor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:01.963883+00:00
-- url     : https://prove2.me/theorems/3c77e230-7785-45e6-aa29-5ddeffd5c5bd
-- title:
--   Proof of Lemma 2, p. 11 — an odd composite M has a divisor p with 3 ≤ p ≤ M/3
-- statement:
--   Let $M$ be an odd composite number (odd, greater than $1$, and not prime). Then $M$ has a divisor $p$ with
--   $$3 \le p \le \frac{M}{3}.$$
--
--   Such a $p$ is a non-trivial divisor of $M$; it supplies a feasible point of problem (4) whose value is well below $M$.
--
--   **Formalization Note** The paper prints "$3 \le p < M/3$", which is false for $M = 9$, whose only non-trivial divisor is $3 = M/3$. The statement here uses $p \le M/3$, written as $3p \le M$; this suffices for the next step of the proof. Non-triviality ($1 < p < M$) follows from $3 \le p$ and $3p \le M$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 11, §2.2, proof of Lemma 2, "Optimal replenishment cycle for item 1", second sentence (printed "< M/3", corrected to "≤ M/3")

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting

namespace JRPHard.Periodic

theorem exists_small_divisor (M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime) :
    ∃ p : ℕ, p ∣ M ∧ 3 ≤ p ∧ 3 * p ≤ M := by sorry

end JRPHard.Periodic
