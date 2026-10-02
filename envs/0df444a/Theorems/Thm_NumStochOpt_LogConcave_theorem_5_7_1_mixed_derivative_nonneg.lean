-- Prove2me | Theorems.Thm_NumStochOpt_LogConcave_theorem_5_7_1_mixed_derivative_nonneg
-- name    : NumStochOpt.LogConcave.theorem_5_7_1_mixed_derivative_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:10:28.367654+00:00
-- url     : https://prove2.me/theorems/2fe705a5-528a-47ec-a4a9-4486640c637e
-- title:
--   Theorem 5.7.1 — the bivariate polynomial distribution has a nonnegative mixed derivative, (5.21)
-- statement:
--   Take $n = 2$ in the polynomial distribution (5.19): for $N \ge 1$, constants $c_i > 0$ and exponents $\alpha_{i1}, \alpha_{i2} \le 0$ with $\alpha_{i1} + \alpha_{i2} < 0$ ($i = 1, \dots, N$), let
--
--   $$
--   F(z_1, z_2) = \frac{1}{\sum_{i=1}^{N} c_i\, z_1^{\alpha_{i1}} z_2^{\alpha_{i2}}}, \qquad 0 < z_1, z_2 \le 1 .
--   $$
--
--   Assume that, across the $N$ terms, the exponents of $z_1$ and of $z_2$ are oppositely ordered:
--
--   $$
--   \alpha_{11} \le \alpha_{21} \le \dots \le \alpha_{N1}, \qquad \alpha_{12} \ge \alpha_{22} \ge \dots \ge \alpha_{N2}.
--   $$
--
--   Then the mixed second derivative of $F$ is nonnegative in the open unit square:
--
--   $$
--   \frac{\partial^2 F(z_1, z_2)}{\partial z_1\, \partial z_2} \ge 0 \qquad \text{for } 0 < z_1, z_2 < 1 . \tag{5.21}
--   $$
--
--   This is the property the book identifies as the only one to be checked for $F$ to be a probability distribution function in the unit square; it makes $F$ assign nonnegative mass to every rectangle.
--
--   **Formalization Note** The book prints the ordering hypothesis as $\alpha_{11} \le \alpha_{12} \le \dots \le \alpha_{1n}$, $\alpha_{21} \ge \alpha_{22} \ge \dots \ge \alpha_{2n}$, with the indices transposed relative to (5.19) and $n$ in place of $N$; its proof (the covariance of the sequences of $z_1$- and $z_2$-exponents under the weights $\lambda_i$, p. 135) shows the intended condition is the one displayed above, and that is what is formalized (`Monotone` in the term index for the $z_1$-exponents, `Antitone` for the $z_2$-exponents; the exponent arrays are `α i 0` and `α i 1`). The theorem claims "is a probability distribution function"; the book proves only (5.21) and asserts the remaining properties (normalisation $F(1,1) = 1$ needs $\sum_i c_i = 1$, which the book does not assume), so the formal statement is (5.21). The mixed derivative is the iterated one-variable derivative `deriv (fun s => deriv (fun t => F(s,t)) z₂) z₁`; $F$ is smooth on the open quadrant, so both derivatives exist there.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, §5.7, p. 133, Theorem 5.7.1 and Eq. (5.21) (proof on pp. 133-135)

import Mathlib
import Definitions.Def_NumStochOpt_LogConcave_polyDistF

namespace NumStochOpt.LogConcave

theorem theorem_5_7_1_mixed_derivative_nonneg {N : ℕ} (hN : 0 < N)
    (c : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (α : Fin N → Fin 2 → ℝ) (hα : ∀ i j, α i j ≤ 0) (hα_sum : ∀ i, ∑ j, α i j < 0)
    (hα_mono : Monotone (fun i => α i 0)) (hα_anti : Antitone (fun i => α i 1))
    (z₁ z₂ : ℝ) (hz₁ : 0 < z₁) (hz₁' : z₁ < 1) (hz₂ : 0 < z₂) (hz₂' : z₂ < 1) :
    0 ≤ deriv (fun s => deriv (fun t => polyDistF c α ![s, t]) z₂) z₁ := by sorry

end NumStochOpt.LogConcave
