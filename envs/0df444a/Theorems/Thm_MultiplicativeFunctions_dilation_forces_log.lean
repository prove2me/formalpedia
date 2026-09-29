-- Prove2me | Theorems.Thm_MultiplicativeFunctions_dilation_forces_log
-- name    : MultiplicativeFunctions.dilation_forces_log
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:49.21181+00:00
-- url     : https://prove2.me/theorems/7ab5b1d7-b66c-490c-89fe-9002b829c978
-- title:
--   A dilation-covariant weight is forced to be $1/n$
-- statement:
--   **Dilation covariance pins a weight down completely.**
--
--   Suppose $w : \mathbb{N} \to \mathbb{R}$ satisfies, for all $q, n \ge 1$,
--
--   $$w(qn) \;=\; \frac{w(n)}{q}.$$
--
--   Then $w$ is determined by its value at $1$:
--
--   $$w(n) \;=\; \frac{w(1)}{n} \qquad (n \ge 1).$$
--
--   The proof is immediate — take $n = 1$ in the hypothesis — but the statement is the useful
--   form: it says the **only** dilation-covariant weights are the multiples of the harmonic weight
--   $1/n$, with no freedom beyond the single constant $w(1)$.
--
--   This rigidity is what makes the harmonic weight canonical in multiplicative number theory.
--   Averages of the form $\sum_n w(n) f(n)$ that are required to behave predictably under
--   $n \mapsto qn$ — as in logarithmic averaging, where $\sum_{n \le x} f(n)/n$ replaces
--   $\sum_{n\le x} f(n)$ — have no choice about the weight. It is the structural reason logarithmic
--   density appears in the Chowla and Elliott conjectures, where dilation invariance of the
--   averaging is exactly what the entropy method exploits.
--
--   **Formalization note.** The hypothesis and conclusion are restricted to $n \ge 1$, avoiding the
--   value $w(0)$, which is unconstrained.
-- source:
--   Arising in the logarithmic-averaging / Chowla circle; cf. Tao, *The logarithmically averaged Chowla and Elliott conjectures* (2016). Lean proof extracted from `Salt/Entropy/Chowla/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MultiplicativeFunctions

theorem dilation_forces_log (w : ℕ → ℝ)
    (hcov : ∀ q n, 1 ≤ q → 1 ≤ n → w (q * n) = w n / (q : ℝ)) :
    ∀ n, 1 ≤ n → w n = w 1 / (n : ℝ) := by sorry

end MultiplicativeFunctions
