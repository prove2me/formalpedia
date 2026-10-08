-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_theorem_3
-- name    : GenEmpLik.Coverage.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:49:15.679984+00:00
-- url     : https://prove2.me/theorems/7358e5fc-3986-4f02-9101-a582a6fd1006
-- title:
--   Theorem 3 — exact coverage of the optimal value
-- statement:
--   Let $\mathcal X\subset\mathbb R^d$ be nonempty and compact, let the losses be measurable and satisfy Assumption B with $\mathbb E_{P_0}[M^2]<\infty$, and suppose $\mathbb E_{P_0}[|\ell(x_0;\xi)|^2]<\infty$ for some $x_0\in\mathcal X$. Let $f$ satisfy Assumption A, let the observations be i.i.d. with law $P_0$, and suppose the population optimizer $x^\star$ is unique with $\operatorname{Var}_{P_0}(\ell(x^\star;\xi))>0$. For $\rho\ge0$,
--
--   $$P^*\!\left(T_{\rm opt}(P_0)\in\{T_{\rm opt}(p):D_f(p\|\widehat P_n)\le\rho/n\}\right)\longrightarrow P(\chi_1^2\le\rho).$$
--
--   The theorem calibrates the empirical likelihood confidence set for the optimal value with a one degree of freedom chi square law.
--
--   **Formalization Note** The variance condition is needed for the result to hold: a deterministic loss has coverage one but a nontrivial chi square target. The set uses weights on the sample, and $P^*$ is outer probability.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 8, Theorem 3

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall
import Definitions.Def_GenEmpLik_Coverage_confidenceSet
import Definitions.Def_GenEmpLik_Coverage_influence
import Definitions.Def_GenEmpLik_Coverage_remainder
import Definitions.Def_GenEmpLik_Coverage_robustUpper
import Definitions.Def_GenEmpLik_Coverage_uniqueOptimizer
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open MeasureTheory ProbabilityTheory Filter Topology

namespace GenEmpLik.Coverage

/-- Theorem 3, p. 8: asymptotically exact coverage of the optimal value. -/
theorem theorem_3
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (M : Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hA : AssumptionA f)
    (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hℓ2 : ∃ x0 ∈ X, Integrable (fun z => ℓ x0 z ^ 2) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hunique : HasUniqueOptimizer X ℓ (μ.map (ξ 0)))
    (hvar : 0 < variance (ℓ (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique))
      (μ.map (ξ 0))) :
    Tendsto (fun n : ℕ => μ {ω |
      optimalValue X ℓ (μ.map (ξ 0)) ∈
        confidenceSet X ℓ f ρ (fun i : Fin n => ξ i ω)})
      atTop (𝓝 (gaussianReal 0 1 {x : ℝ | x ^ 2 ≤ ρ})) := by sorry

end GenEmpLik.Coverage
