-- Prove2me | Theorems.Thm_GeometricSums_hasSum_sq_mul_geometric_inv
-- name    : GeometricSums.hasSum_sq_mul_geometric_inv
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:04.166531+00:00
-- url     : https://prove2.me/theorems/6f4e13ac-3b47-4336-8590-fbc779d3f5c2
-- title:
--   The closed form of $\sum (k+1)^2 x^k$ at $x = 1/p$
-- statement:
--   **A quadratically weighted geometric series in closed form.**
--
--   For an integer $p \ge 2$, writing $x = 1/p \in (0, \tfrac12]$,
--
--   $$\sum_{k=0}^{\infty} (k+1)^{2}\,x^{k} \;=\; \frac{1+x}{(1-x)^{3}} .$$
--
--   This is the second derivative-type identity in the geometric family: differentiating
--   $\sum_k x^{k} = (1-x)^{-1}$ once gives $\sum_k (k+1)x^{k} = (1-x)^{-2}$, and applying the
--   operator $x\frac{d}{dx}$ again and re-indexing produces the stated closed form, the numerator
--   $1+x$ being what distinguishes $\sum (k+1)^2 x^k$ from $\sum (k+1)k\,x^{k}$.
--
--   Restricting to $x = 1/p$ with $p \ge 2$ keeps $|x| < 1$, so the series converges absolutely and
--   the identity is an honest `HasSum` rather than a formal power-series manipulation.
--
--   Sums of this shape are the "local factors" appearing when a multiplicative quantity weighted by
--   the square of the exponent — such as a divisor-function moment or the local density in a
--   sieve — is expanded as an Euler product over primes; the closed form is what makes the
--   resulting product estimable.
--
--   **Formalization note.** `HasSum` asserts unconditional summability to the stated value, which
--   is stronger than convergence of the partial sums; the hypothesis $2 \le p$ makes $(p:\mathbb{R})^{-1} \le 1/2$.
-- source:
--   Classical; the weighted geometric series, cf. Mathlib's `hasSum_coe_mul_geometric_of_norm_lt_one`. Lean proof extracted from `Salt/MR/ShiuMoment.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem hasSum_sq_mul_geometric_inv {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k)
      ((1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3) := by sorry

end GeometricSums
