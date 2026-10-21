-- Prove2me | Theorems.Thm_NatureSLT_Kernels_hermite_kernel_multidim
-- name    : NatureSLT.Kernels.hermite_kernel_multidim
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:11.252882+00:00
-- url     : https://prove2.me/theorems/19a2bd0a-57fe-439a-af7f-25f7612a574b
-- title:
--   Eq. (6.26) — the $n$-dimensional Hermite kernel as one exponential (as printed)
-- statement:
--   Let $n \ge 0$, $0 \le q < 1$, and let $x = (x^1, \dots, x^n)$ and $y = (y^1, \dots, y^n)$ be vectors of $\mathbb R^n$, with inner product $(x * y) = \sum_i x^i y^i$ and Euclidean norm $|x - y|$. The second equality of (6.26) claims
--
--   $$\prod_{i=1}^{n} \frac{1}{\sqrt{\pi(1 - q^2)}} \exp\left\{\frac{2x^iy^iq}{1 + q} - \frac{(x^i - y^i)^2 q^2}{1 - q^2}\right\} = \frac{1}{(1 - q^2)^{n/2}} \exp\left\{\frac{2(x * y)q}{1 + q} - \frac{|x - y|^2 q^2}{1 - q^2}\right\}.$$
--
--   The left side is the product of $n$ one-dimensional Hermite kernels (6.24), which by Theorem 6.1 is the kernel of the tensor-product Hermite basis; the right side is the form the book uses to motivate the semilocal kernels (6.27).
--
--   **Formalization Note** Only the second "=" of (6.26) is stated; the first is Theorem 6.1 applied to (6.24). The range $0 \le q < 1$ is that of (6.24). This statement is believed to be false as printed for $n \ge 1$: the product of the prefactors is $(\pi(1-q^2))^{-n/2}$, and the factor $\pi^{-n/2}$ is missing on the right (see the corrected variant). The power $n/2$ is a real power of a positive number.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 193, Eq. (6.26)

import Mathlib

namespace NatureSLT.Kernels

/-- Eq. (6.26), second equality (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
§6.3.2, p. 193), as printed: for `x, y ∈ ℝⁿ` and `0 ≤ q < 1`,
`Π_{i=1}^n (π(1 - q²))^{-1/2} exp{2x^i y^i q/(1 + q) - (x^i - y^i)² q²/(1 - q²)}
  = (1 - q²)^{-n/2} exp{2(x * y) q/(1 + q) - |x - y|² q²/(1 - q²)}`,
where `x * y` is the inner product and `|x - y|` the Euclidean norm. -/
theorem hermite_kernel_multidim (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ∏ i : Fin n, (1 / Real.sqrt (Real.pi * (1 - q ^ 2)) *
        Real.exp (2 * x i * y i * q / (1 + q) - (x i - y i) ^ 2 * q ^ 2 / (1 - q ^ 2))) =
      1 / (1 - q ^ 2) ^ ((n : ℝ) / 2) *
        Real.exp (2 * inner ℝ x y * q / (1 + q) - ‖x - y‖ ^ 2 * q ^ 2 / (1 - q ^ 2)) := by sorry

end NatureSLT.Kernels
