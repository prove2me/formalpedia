-- Prove2me | Theorems.Thm_NatureSLT_Kernels_dirichlet_kernel
-- name    : NatureSLT.Kernels.dirichlet_kernel
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:09.07753+00:00
-- url     : https://prove2.me/theorems/77378eb9-2def-48e0-b4c3-4f6f65cc94c7
-- title:
--   §6.5 — the Dirichlet kernel $K_N$ in closed form (as printed, p. 197)
-- statement:
--   For an integer $N \ge 0$ and real numbers $x$, $x_i$ with $x - x_i \notin 2\pi\mathbb Z$, the kernel of the $(2N + 1)$-dimensional Fourier feature map $u = (1/\sqrt2, \sin x, \dots, \sin Nx, \cos x, \dots, \cos Nx)$ is claimed to satisfy
--
--   $$K_N(x, x_i) = \frac12 + \sum_{k=1}^{N} (\sin kx \sin kx_i + \cos kx \cos kx_i) = \frac12 + \sum_{k=1}^{N} \cos k(x - x_i) = \frac{\sin \frac{2N + 1}{2}(x - x_i)}{\sin \frac{x - x_i}{2}}.$$
--
--   The book uses this closed form for the kernel of the truncated Fourier expansion (6.31).
--
--   **Formalization Note** The condition $x - x_i \notin 2\pi\mathbb Z$ is written as $\sin((x - x_i)/2) \ne 0$; it excludes the points where the right side is $0/0$. Both equalities of the display are stated. This statement is believed to be false as printed: the correct denominator is $2 \sin((x - x_i)/2)$ (see the corrected variant).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 197, Section 6.5 (display following (6.31))

import Mathlib

namespace NatureSLT.Kernels

/-- The Dirichlet kernel display (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
§6.5, p. 197, unnumbered), as printed: for `N ≥ 0` and real `x, x_i` with
`x - x_i ∉ 2πℤ` (where the right side's denominator is nonzero),
`K_N(x, x_i) = 1/2 + Σ_{k=1}^N (sin kx sin kx_i + cos kx cos kx_i)
  = 1/2 + Σ_{k=1}^N cos k(x - x_i) = sin((2N+1)/2 (x - x_i)) / sin((x - x_i)/2)`. -/
theorem dirichlet_kernel (N : ℕ) (x xi : ℝ) (hx : Real.sin ((x - xi) / 2) ≠ 0) :
    (1 / 2 + ∑ k ∈ Finset.Icc 1 N,
        (Real.sin (k * x) * Real.sin (k * xi) + Real.cos (k * x) * Real.cos (k * xi)) =
      1 / 2 + ∑ k ∈ Finset.Icc 1 N, Real.cos (k * (x - xi))) ∧
    1 / 2 + ∑ k ∈ Finset.Icc 1 N, Real.cos (k * (x - xi)) =
      Real.sin ((2 * N + 1) / 2 * (x - xi)) / Real.sin ((x - xi) / 2) := by sorry

end NatureSLT.Kernels
