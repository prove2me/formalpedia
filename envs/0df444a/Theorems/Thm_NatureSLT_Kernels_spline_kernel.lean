-- Prove2me | Theorems.Thm_NatureSLT_Kernels_spline_kernel
-- name    : NatureSLT.Kernels.spline_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:01.105574+00:00
-- url     : https://prove2.me/theorems/f0f9bd0b-3fac-4e52-941b-84c34526f6af
-- title:
--   Eq. (6.30) — the kernel of splines of order $d$ with infinitely many nodes, and the linear case $K_1$
-- statement:
--   Let $0 < a < \infty$, let $x_j, x_i \in [0, a]$, write $x_j \wedge x_i = \min(x_j, x_i)$, and let $(x - t)^d_+$ be the truncated power. For splines of order $d \ge 0$ with an infinite number of nodes on $(0, a)$ the generating kernel has the closed form
--
--   $$K(x_j, x_i) = \int_0^a (x_j - t)^d_+ (x_i - t)^d_+\, dt + \sum_{r=0}^{d} x_j^r x_i^r = \sum_{r=0}^{d} \frac{C_d^r}{2d - r + 1} (x_j \wedge x_i)^{2d - r + 1} |x_j - x_i|^r + \sum_{r=0}^{d} x_j^r x_i^r,$$
--
--   where $C_d^r$ is the binomial coefficient. In particular, for a linear spline ($d = 1$),
--
--   $$K_1(x_j, x_i) = 1 + x_j x_i + \frac12 |x_j - x_i| (x_j \wedge x_i)^2 + \frac{(x_j \wedge x_i)^3}{3}.$$
--
--   This makes the infinite-node spline kernel computable in finitely many operations.
--
--   **Formalization Note** The two middle lines of the book's display are intermediate steps and are not stated; the first and last lines are (the third line has a misprinted lower index, finding F4). The book's last line prints $|x_j - x_j|^r$, a typo for $|x_j - x_i|^r$ (finding F6): read literally every $r \ge 1$ term vanishes, which contradicts the third line and the book's own $K_1$; the corrected $|x_j - x_i|^r$ is stated. Likewise the first line's $\sum_r x^r x_i^r$ is read as $\sum_r x_j^r x_i^r$. The points lie in $[0, a]$, the interval on which the splines are defined (§6.4.1). In the sums $x^0 = 1$, including at $x = 0$. The integral is the interval integral from $0$ to $a$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 196, Eq. (6.30)

import Mathlib
import Definitions.Def_NatureSLT_Kernels_truncPow

namespace NatureSLT.Kernels

/-- Eq. (6.30) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.4.2, p. 196),
first line = last line, and the linear-spline case `K₁`. For splines of order `d ≥ 0` with an
infinite number of nodes on `(0, a)`, `0 < a < ∞`, and points `x_j, x_i ∈ [0, a]`, with
`x_j ∧ x_i = min(x_j, x_i)` and `C_d^r` the binomial coefficient:
`∫_0^a (x_j - t)^d_+ (x_i - t)^d_+ dt + Σ_{r=0}^d x_j^r x_i^r
  = Σ_{r=0}^d C_d^r/(2d - r + 1) (x_j ∧ x_i)^{2d-r+1} |x_j - x_i|^r + Σ_{r=0}^d x_j^r x_i^r`,
and for `d = 1` the kernel equals
`1 + x_j x_i + (1/2)|x_j - x_i|(x_j ∧ x_i)² + (x_j ∧ x_i)³/3`.
(`0^0 = 1` in the sums, as the book's `r = 0` terms require.) The book's last line prints
`|x_j - x_j|^r`, a typo for `|x_j - x_i|^r` (the third line and `K₁` confirm it); the corrected
factor is stated. The first line's `Σ x^r x_i^r` is read as `Σ x_j^r x_i^r`. -/
theorem spline_kernel (a : ℝ) (ha : 0 < a) (xj xi : ℝ) (hxj : xj ∈ Set.Icc 0 a)
    (hxi : xi ∈ Set.Icc 0 a) :
    (∀ d : ℕ,
      (∫ t in (0 : ℝ)..a, truncPow d xj t * truncPow d xi t) +
          ∑ r ∈ Finset.range (d + 1), xj ^ r * xi ^ r =
        ∑ r ∈ Finset.range (d + 1),
            (d.choose r : ℝ) / (2 * (d : ℝ) - r + 1) * min xj xi ^ (2 * d - r + 1) *
              |xj - xi| ^ r +
          ∑ r ∈ Finset.range (d + 1), xj ^ r * xi ^ r) ∧
    (∫ t in (0 : ℝ)..a, truncPow 1 xj t * truncPow 1 xi t) +
        ∑ r ∈ Finset.range 2, xj ^ r * xi ^ r =
      1 + xj * xi + 1 / 2 * |xj - xi| * min xj xi ^ 2 + min xj xi ^ 3 / 3 := by sorry

end NatureSLT.Kernels
