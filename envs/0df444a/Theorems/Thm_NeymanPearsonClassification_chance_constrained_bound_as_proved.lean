-- Prove2me | Theorems.Thm_NeymanPearsonClassification_chance_constrained_bound_as_proved
-- name    : NeymanPearsonClassification.chance_constrained_bound_as_proved
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:47:34.231986+00:00
-- url     : https://prove2.me/theorems/547e13ed-3521-4aeb-8950-f87d734c1515
-- title:
--   Theorem 5.1 (as proved): sampled convexified chance constrained programs
-- statement:
--   Let $\delta,\alpha\in(0,1/2)$, $L>0$, and let $\varphi$ be an $L$-Lipschitz convex surrogate. Let $g_1,\dots,g_M:\Xi\to[-1,1]$, $M\ge2$, be measurable, put $F(\lambda,\xi)=\sum_j\lambda_jg_j(\xi)$, and let $f$ be a real-valued convex function on the simplex $\Lambda$. Let $\xi_1,\dots,\xi_n$, $n\ge1$, be i.i.d. copies of $\xi$, let $\kappa=4\sqrt2\,L\sqrt{\log(2M/\delta)}$, and let $\tilde\lambda$ be any solution of
--
--   $$\min_{\lambda\in\Lambda}f(\lambda)\quad\text{s.t.}\quad\sum_{i=1}^n\varphi(F(\lambda,\xi_i))\le n\alpha-\kappa\sqrt n.$$
--
--   Let $f^*_\varphi$ be the optimal value of $\min_{\lambda\in\Lambda}f(\lambda)$ s.t. $E[\varphi(F(\lambda,\xi))]\le\alpha$. Then, with probability at least $1-2\delta$:
--
--   1. $\tilde\lambda$ is feasible for the chance constrained problem (5.1): $\mathbb P\{F(\tilde\lambda,\xi)\le0\}\ge1-\alpha$.
--   2. If $\varepsilon\in(0,1)$ is such that $E[\varphi(F(\lambda,\xi))]\le\varepsilon\alpha$ for some $\lambda\in\Lambda$, and $n\ge(4\kappa/((1-\varepsilon)\alpha))^2$, then
--   $$f(\tilde\lambda)-f^*_\varphi\le\frac{4\,(\sup_\Lambda f-\inf_\Lambda f)\,\kappa}{(1-\varepsilon)\alpha\sqrt n}.$$
--
--   **Formalization Note** The paper prints the constant $\varphi(1)$ in place of $\sup_\Lambda f-\inf_\Lambda f$. That version is false for a general convex $f$: multiplying $f$ by $c>0$ multiplies the left side by $c$ and leaves $\varphi(1)$ unchanged. The proof the paper refers to (that of Theorem 4.2, through Proposition 4.1) bounds $\gamma(\varepsilon\alpha)-\gamma(\alpha-\nu)$ by the range of the objective, which is $\varphi(1)$ only when the objective takes values in $[0,\varphi(1)]$, as $R^+_\varphi$ does. The statement here is the one that proof establishes. As in the paper, the event in item 2 is uniform in $\varepsilon$. $f^*_\varphi$ is an infimum, and "any solution" is stated uniformly over all solutions.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 5, Theorem 5.1, eqs. (5.1), (5.7), p. 12 (proof referred to Section 6.4)

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem chance_constrained_bound_as_proved {Xi : Type*} [MeasurableSpace Xi] {M n : ℕ}
    (hM : 2 ≤ M) (hn : 1 ≤ n) (g : Fin M → Xi → ℝ) (hg : IsBaseFamily g)
    (Pxi : Measure Xi) [IsProbabilityMeasure Pxi]
    (f : (Fin M → ℝ) → ℝ) (hf : ConvexOn ℝ (stdSimplex ℝ (Fin M)) f)
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (L : ℝ) (hL : 0 < L) (hLip : LipschitzOnWith (Real.toNNReal L) φ (Set.Icc (-1) 1))
    (δ α : ℝ) (hδ : δ ∈ Set.Ioo 0 (1 / 2)) (hα : α ∈ Set.Ioo 0 (1 / 2))
    {Omega : Type*} [MeasurableSpace Omega] (μ : Measure Omega) [IsProbabilityMeasure μ]
    (xi : Fin n → Omega → Xi) (hxim : ∀ i, Measurable (xi i))
    (hxiind : iIndepFun xi μ) (hxilaw : ∀ i, μ.map (xi i) = Pxi) :
    μ {ω | ¬ ∀ lam, IsScenarioSolution g φ f α (kappa L M δ) (fun i => xi i ω) lam →
      IsChanceFeasible g Pxi α lam ∧
      ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        (∃ l ∈ stdSimplex ℝ (Fin M), phiTypeI Pxi φ (convComb g l) ≤ ε * α) →
        (4 * kappa L M δ / ((1 - ε) * α)) ^ 2 ≤ n →
        f lam - ccpOptValue g Pxi φ f α ≤
          4 * (sSup (f '' stdSimplex ℝ (Fin M)) - sInf (f '' stdSimplex ℝ (Fin M))) *
            kappa L M δ / ((1 - ε) * α * Real.sqrt n)} ≤ ENNReal.ofReal (2 * δ) := by sorry

end NeymanPearsonClassification
