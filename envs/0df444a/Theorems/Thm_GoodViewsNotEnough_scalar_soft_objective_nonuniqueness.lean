-- Prove2me | Theorems.Thm_GoodViewsNotEnough_scalar_soft_objective_nonuniqueness
-- name    : GoodViewsNotEnough.scalar_soft_objective_nonuniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:50:34.385868+00:00
-- url     : https://prove2.me/theorems/d58e5da9-d25c-4e3f-b89c-ab6fc4c9d80f
-- title:
--   Theorem 4 (as proved): scalar soft-objective nonuniqueness
-- statement:
--   On the four-state scalar model, let the domain $X$ be either $\mathbb{R}^4$ or the centred domain $X_0=\{x:\sum_ix_i=0\}$. Each objective below attains its minimum on $X$. Moreover, for every global minimiser $x$, one of the within-scene swaps $T_+=(12)$, $T_-=(34)$ gives a point $x\circ T\in X$ with the same objective value and $x\circ T\notin\{x,-x\}$. The objectives are:
--
--   1. $P_\pi+\gamma D_{\rm an}(\mu_x)$ and $P_\pi+\gamma D_{\rm gr}(\mu_x)$ for $\gamma\ge20$;
--   2. $P_\pi+\gamma D_{\rm an}(\mu_x)$ for $\gamma\ge16$;
--   3. $P_\pi+\alpha R_{N,\nu}(\mu_x)$, for either frequency measure, whenever $\alpha>0$ and
--
--   $$\alpha\Big(\frac{17N}{1000}-\frac{251}{100}\Big)>\frac{121}{400}.$$
--
--   Scalar rotations act only by $x\mapsto-x$, so each of these objectives has global minimisers that are not unique up to rotation.
--
--   **Formalization Note** The hypothesis $\alpha>0$ is not printed with condition (13). The proof uses it, and it holds for the mixing weights $\alpha=\lambda/(1-\lambda)$, $0<\lambda<1$, to which the theorem is applied. Without it, (13) can hold with $\alpha<0$ and $N\le147$, and the conclusion can then fail: for $N=1$, $\alpha=-1$ the global minimiser is scene-only.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix B.3, Theorem 4, eq. (13), p. 13

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem scalar_soft_objective_nonuniqueness :
    ∀ X ∈ ({Set.univ, centeredDomain} : Set (Set (Fin 4 → ℝ))),
      (∀ γ : ℝ, 20 ≤ γ →
        SwapNonuniqueness (detObjective analyticFreq γ) X ∧
        SwapNonuniqueness (detObjective gridFreq γ) X) ∧
      (∀ γ : ℝ, 16 ≤ γ → SwapNonuniqueness (detObjective analyticFreq γ) X) ∧
      (∀ (N : ℕ) (α : ℝ), 0 < α → 121 / 400 < α * (17 * (N : ℝ) / 1000 - 251 / 100) →
        SwapNonuniqueness (iidObjective analyticFreq N α) X ∧
        SwapNonuniqueness (iidObjective gridFreq N α) X) := by sorry

end GoodViewsNotEnough
