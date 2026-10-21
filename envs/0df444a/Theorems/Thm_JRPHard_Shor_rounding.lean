-- Prove2me | Theorems.Thm_JRPHard_Shor_rounding
-- name    : JRPHard.Shor.rounding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:37.88678+00:00
-- url     : https://prove2.me/theorems/4e11425a-a963-4272-af4b-5184401d175c
-- title:
--   Proof of Lemma 3, p. 15 — rounded endpoints
-- statement:
--   Let $M$ be a natural number and $0<L\le U$ be real. Suppose $\lceil L\rceil\le\lfloor U\rfloor\le M$ and $L+U<2\sqrt{2LU}$. Then
--   $$\bigl(\exists d\mid M:\ \lceil L\rceil\le d\le\lfloor U\rfloor\bigr)\quad\Longleftrightarrow\quad\bigl(\exists d\mid M:\ L\le d\le U\bigr),$$
--   and $(M,\lceil L\rceil,\lfloor U\rfloor)$ meets every RangeDivisor instance condition.
--   This states the numerical validity of using integer endpoints. The stated ordering of rounded endpoints is needed for the second conclusion.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 15, proof of Lemma 3, rounding sentence

import Mathlib
import Definitions.Def_JRPHard_Shor_DecisionProblems

namespace JRPHard.Shor

/-- Proof of Lemma 3, p. 15: rounding the two endpoints preserves the divisor
    question and, under the interval side conditions, gives a RangeDivisor instance. -/
theorem rounding (M : ℕ) (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (hceil : ⌈L⌉₊ ≤ ⌊U⌋₊) (hbound : ⌊U⌋₊ ≤ M)
    (hrange : L + U < 2 * Real.sqrt (2 * L * U)) :
    (JRPHard.RangeDiv.HasDivisorIn M ⌈L⌉₊ ⌊U⌋₊ ↔
      ∃ d : ℕ, d ∣ M ∧ L ≤ (d : ℝ) ∧ (d : ℝ) ≤ U) ∧
    JRPHard.RangeDiv.IsRangeDivisorInstance M ⌈L⌉₊ ⌊U⌋₊ := by sorry

end JRPHard.Shor
