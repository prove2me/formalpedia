-- Prove2me | Theorems.Thm_NatureSLT_Kernels_regularized_fourier_kernel
-- name    : NatureSLT.Kernels.regularized_fourier_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:13.465421+00:00
-- url     : https://prove2.me/theorems/10a38ea2-768c-4e81-8078-c44f2a46baf1
-- title:
--   Eq. (6.33) — the kernel of the Fourier expansion regularized by $1/(1 + \gamma^2 k^2)$
-- statement:
--   Let $\gamma > 0$ and let $x_i$, $x_j$ be real numbers with $0 \le |x_i - x_j| \le 2\pi$. The kernel of the regularized Fourier expansion $f(x) = a_0/\sqrt2 + \sum_{k \ge 1} (a_k \cos kx + b_k \sin kx)/(1 + \gamma^2 k^2)$ is given by a convergent series, and
--
--   $$K(x_i, x_j) = \frac12 + \sum_{k=1}^{\infty} \frac{\cos kx_i \cos kx_j + \sin kx_i \sin kx_j}{1 + \gamma^2 k^2} = \frac{\pi}{2\gamma}\, \frac{\operatorname{ch} \frac{\pi - |x_i - x_j|}{\gamma}}{\operatorname{sh} \frac{\pi}{\gamma}},$$
--
--   where $\operatorname{ch}$ and $\operatorname{sh}$ are the hyperbolic cosine and sine.
--
--   This closed form makes the kernel of the second regularizing scheme of §6.5.1 computable in finitely many operations; the parameter $\gamma$ sets the strength of the regularization.
--
--   **Formalization Note** The page does not state the range of $\gamma$; $\gamma > 0$ is assumed, as for a regularization parameter (at $\gamma = 0$ the right side is undefined). The range $|x_i - x_j| \le 2\pi$ is the book's; outside it the left side is $2\pi$-periodic in $x_i - x_j$ and the right side is not. The series is asserted to converge; the sum over $k \ge 1$ is written in Lean over $k = 0, 1, 2, \dots$ with $k + 1$ in place of $k$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 198, Eq. (6.33)

import Mathlib

namespace NatureSLT.Kernels

/-- Eq. (6.33) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.5.1, p. 198):
for `γ > 0` and real `x_i, x_j` with `0 ≤ |x_i - x_j| ≤ 2π`, the series
`Σ_{k=1}^∞ (cos kx_i cos kx_j + sin kx_i sin kx_j)/(1 + γ²k²)` converges and
`K(x_i, x_j) = 1/2 + Σ_{k=1}^∞ (cos kx_i cos kx_j + sin kx_i sin kx_j)/(1 + γ²k²)
  = (π/(2γ)) ch((π - |x_i - x_j|)/γ) / sh(π/γ)`.
The page does not state the range of `γ`; `γ > 0` is added (at `γ = 0` the right side is
undefined). The sum over `k ≥ 1` is written over `k : ℕ` with `k + 1` in place of `k`. -/
theorem regularized_fourier_kernel (γ : ℝ) (hγ : 0 < γ) (xi xj : ℝ)
    (hx : |xi - xj| ≤ 2 * Real.pi) :
    Summable (fun k : ℕ =>
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) / (1 + γ ^ 2 * (k + 1) ^ 2)) ∧
    1 / 2 + ∑' k : ℕ,
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) / (1 + γ ^ 2 * (k + 1) ^ 2) =
      Real.pi / (2 * γ) * Real.cosh ((Real.pi - |xi - xj|) / γ) / Real.sinh (Real.pi / γ) := by sorry

end NatureSLT.Kernels
