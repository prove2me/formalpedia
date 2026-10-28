-- Prove2me | Theorems.Thm_LL_Decomp1525c_distribution_of
-- name    : LL_Decomp1525c.distribution_of
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:09:11.795301+00:00
-- url     : https://prove2.me/theorems/b09b8990-0732-441f-96c8-023c21a28fd4
-- title:
--   Assemble the conditional distribution bound
-- statement:
--   Assume $|\theta(y)-y|<y/(40\log y)$ for every real $y\ge678407$, where $\theta$ is Chebyshev's prime logarithm sum. Also assume that for every real $z\ge10^{52}$, $|\Psi(z)-\sum_{p\in P_1(z)}\log p\int_{z-p}^{2z-p}du/\log u|<z^2/(12\log^2z)$. Conditional on these two inputs, every real $x\ge10^{52}$ satisfies $|\Psi(x)-M(x)|<x^2/(5\log^2x)$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_PsiV
import Definitions.Def_LL_Decomp1525c_mainIntegralV
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem distribution_of
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (hPI : ∀ x : ℝ, 10 ^ 52 ≤ x →
      |PsiV x - ∑ p ∈ P1V x, Real.log p * ∫ u in (x - p)..(2 * x - p), 1 / Real.log u|
        < x ^ 2 / (12 * Real.log x ^ 2)) :
    ∀ x : ℝ, 10 ^ 52 ≤ x → |PsiV x - mainIntegralV x| < x ^ 2 / (5 * Real.log x ^ 2) := by sorry
end LL_Decomp1525c
