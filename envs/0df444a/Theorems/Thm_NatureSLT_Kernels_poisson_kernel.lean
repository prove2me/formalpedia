-- Prove2me | Theorems.Thm_NatureSLT_Kernels_poisson_kernel
-- name    : NatureSLT.Kernels.poisson_kernel
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:13.095622+00:00
-- url     : https://prove2.me/theorems/26cd0860-d14a-46d6-8385-182f2d467157
-- title:
--   Eq. (6.32) — the kernel of the regularized Fourier expansion with factors $q^k$
-- statement:
--   Let $0 < q < 1$ and let $x_i$, $x_j$ be real numbers. The kernel of the regularized Fourier expansion $f(x) = a_0/\sqrt2 + \sum_{k \ge 1} q^k (a_k \cos kx + b_k \sin kx)$ is given by convergent series, and
--
--   $$K(x_i, x_j) = \frac12 + \sum_{k=1}^{\infty} q^k (\cos kx_i \cos kx_j + \sin kx_i \sin kx_j) = \frac12 + \sum_{k=1}^{\infty} q^k \cos k(x_i - x_j) = \frac{1 - q^2}{2(1 - 2q\cos(x_i - x_j) + q^2)}.$$
--
--   The factors $q^k$ damp the high frequencies; the closed form shows that the resulting kernel is smooth and concentrated near $x_i = x_j$ as $q \to 1$.
--
--   **Formalization Note** Both series are asserted to converge (summability), and both equalities of the display are stated. The sums over $k \ge 1$ are written in Lean over $k = 0, 1, 2, \dots$ with $k + 1$ in place of $k$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 197, Eq. (6.32)

import Mathlib

namespace NatureSLT.Kernels

/-- Eq. (6.32) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.5.1, p. 197):
for `0 < q < 1` and real `x_i, x_j`, the series
`Σ_{k=1}^∞ q^k (cos kx_i cos kx_j + sin kx_i sin kx_j)` and `Σ_{k=1}^∞ q^k cos k(x_i - x_j)`
converge, and
`K(x_i, x_j) = 1/2 + Σ_{k=1}^∞ q^k (cos kx_i cos kx_j + sin kx_i sin kx_j)
  = 1/2 + Σ_{k=1}^∞ q^k cos k(x_i - x_j) = (1 - q²) / (2(1 - 2q cos(x_i - x_j) + q²))`.
The sums over `k ≥ 1` are written over `k : ℕ` with `k + 1` in place of `k`. -/
theorem poisson_kernel (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (xi xj : ℝ) :
    Summable (fun k : ℕ => q ^ (k + 1) *
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj))) ∧
    Summable (fun k : ℕ => q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj))) ∧
    1 / 2 + ∑' k : ℕ, q ^ (k + 1) *
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) =
      1 / 2 + ∑' k : ℕ, q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj)) ∧
    1 / 2 + ∑' k : ℕ, q ^ (k + 1) * Real.cos ((k + 1) * (xi - xj)) =
      (1 - q ^ 2) / (2 * (1 - 2 * q * Real.cos (xi - xj) + q ^ 2)) := by sorry

end NatureSLT.Kernels
