-- Prove2me | Theorems.Thm_LargeSieve_analytic_large_sieve
-- name    : LargeSieve.analytic_large_sieve
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T04:14:41.673+00:00
-- url     : https://prove2.me/theorems/05ab9246-ae34-437e-b76b-44598dd6c900
-- title:
--   The analytic large sieve inequality for well-spaced exponential sums
-- statement:
--   The **analytic large sieve inequality** bounds the mean square of an exponential sum sampled at
--   well-spaced points by the $\ell^2$ norm of its coefficients.
--
--   $$\sum_{r} \Big|\sum_{n < N} a_n\, e(n\alpha_r)\Big|^2 \;\le\; \bigl(\delta^{-1} + 13N\bigr) \sum_{n < N} |a_n|^2$$
--
--   Here $e(x) = \exp(2\pi i x)$, the coefficients $a_n$ are arbitrary complex numbers, and the sample
--   points $\alpha_1,\dots,\alpha_R$ are real numbers that are **$\delta$-spaced modulo one**: any two
--   distinct points differ by at least $\delta$ in the distance-to-the-nearest-integer metric, with
--   $0 < \delta \le 1/2$.
--
--   The content is that the right-hand side does not depend on the number $R$ of sample points, only on
--   their spacing. A trivial bound would lose a factor of $R$; the large sieve says that separation
--   alone recovers almost everything, giving $\delta^{-1} + O(N)$ in its place. Specialising the
--   $\alpha_r$ to Farey fractions $a/q$ with $q \le Q$ yields the arithmetic large sieve and, through
--   it, the Bombieri–Vinogradov theorem, Linnik's theorem on the least prime in an arithmetic
--   progression, and the standard estimates for minor arcs in the circle method.
--
--   **Formalization note.** The spacing hypothesis is written directly as
--   `δ ≤ |α r - α s - round (α r - α s)|`, which is the distance from $\alpha_r - \alpha_s$ to the
--   nearest integer, and $e(x)$ is written out as `Complex.exp (2 * Real.pi * Complex.I * x)`. The
--   statement therefore needs only Mathlib; no auxiliary definitions are introduced.
-- source:
--   Analytic large sieve inequality. Lean proof from the Salt project by Jason Hickey, Salt/Certs/LargeSieve.lean (https://github.com/jyh/salt, Apache-2.0).

import Mathlib

namespace LargeSieve

/-- The analytic large sieve inequality: for well-spaced real points `α r`, the mean square of an
exponential sum over those points is controlled by the `ℓ²` norm of its coefficients. -/
theorem analytic_large_sieve {R N : ℕ} {δ : ℝ} {α : Fin R → ℝ} (a : ℕ → ℂ)
    (hsp : ∀ r s, r ≠ s → δ ≤ |α r - α s - round (α r - α s)|)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∑ r, ‖∑ n ∈ Finset.range N,
        a n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * α r))‖ ^ 2
      ≤ (δ⁻¹ + 13 * N) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  sorry

end LargeSieve
