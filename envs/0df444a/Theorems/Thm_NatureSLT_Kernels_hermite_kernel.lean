-- Prove2me | Theorems.Thm_NatureSLT_Kernels_hermite_kernel
-- name    : NatureSLT.Kernels.hermite_kernel
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:57.765849+00:00
-- url     : https://prove2.me/theorems/3e899589-0a0f-410a-b3e7-085161b3fafe
-- title:
--   Eq. (6.24) — the regularized Hermite kernel $\sum_i q^i H_i(x)H_i(y)$ in closed form (as printed)
-- statement:
--   Let $P_k(x) = (-1)^k e^{x^2} (d/dx)^k e^{-x^2}$ be the Hermite polynomials and, for normalization constants $\mu_k$, let $H_k(x) = \mu_k P_k(x) e^{-x^2}$ as in (6.23). The claim of (6.24) is that for suitable normalization constants $\mu_0, \mu_1, \dots$, for every $0 \le q < 1$ and all real $x$, $y$, the series below converges and
--
--   $$K(x, y) = \sum_{i=0}^{\infty} q^i H_i(x) H_i(y) = \frac{1}{\sqrt{\pi(1 - q^2)}} \exp\left\{\frac{2xyq}{1 + q} - \frac{(x - y)^2 q^2}{1 - q^2}\right\}.$$
--
--   The book uses this kernel to show how the regularization parameter $q$ controls the kernel: the closer $q$ is to one, the closer $K$ is to the $\delta$-function.
--
--   **Formalization Note** The book chooses $r_i = q^i$ with $0 \le q \le 1$; the value $q = 1$ is excluded because the right side divides by $1 - q^2$. The term $i = 0$ is $H_0(x)H_0(y)$, also at $q = 0$ ($q^0 = 1$). Convergence is stated as `HasSum` (the series converges to the right side). The constants $\mu_k$ are existentially quantified, since the book does not give them. This statement is believed to be false as printed: the Gaussian factor of (6.23) cannot be absorbed by any constants (see the corrected variant).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 192, Eqs. (6.23)–(6.24)

import Mathlib
import Definitions.Def_NatureSLT_Kernels_hermiteH

namespace NatureSLT.Kernels

/-- Eqs. (6.23)–(6.24) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.3.1,
p. 192), as printed: there are normalization constants `μ_k` such that, with
`H_k(x) = μ_k P_k(x) e^{-x²}` and `P_k(x) = (-1)^k e^{x²} (d/dx)^k e^{-x²}`, for every
`0 ≤ q < 1` (the book's `0 ≤ q ≤ 1` for `r_i = q^i`, without `q = 1`, where (6.24) divides by
zero) and all real `x, y`,
`Σ_{i=0}^∞ q^i H_i(x) H_i(y) = (π(1 - q²))^{-1/2} exp{2xyq/(1 + q) - (x - y)² q²/(1 - q²)}`.
`q^0 = 1` also at `q = 0`. The series is stated with `HasSum` (convergence to that value). -/
theorem hermite_kernel :
    ∃ μ : ℕ → ℝ, ∀ q : ℝ, 0 ≤ q → q < 1 → ∀ x y : ℝ,
      HasSum (fun i : ℕ => q ^ i * hermiteH μ i x * hermiteH μ i y)
        (1 / Real.sqrt (Real.pi * (1 - q ^ 2)) *
          Real.exp (2 * x * y * q / (1 + q) - (x - y) ^ 2 * q ^ 2 / (1 - q ^ 2))) := by sorry

end NatureSLT.Kernels
