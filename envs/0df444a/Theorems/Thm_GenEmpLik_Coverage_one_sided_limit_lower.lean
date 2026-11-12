-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_one_sided_limit_lower
-- name    : GenEmpLik.Coverage.one_sided_limit_lower
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T01:49:47.473054+00:00
-- url     : https://prove2.me/theorems/f793a8af-2a77-4869-9754-5dc17c049705
-- title:
--   Lower one-sided coverage limit for the optimal value
-- statement:
--   Let $\mathcal X\subset\mathbb R^d$ be nonempty and compact, let the losses $\ell(\cdot;\xi)$ be measurable and satisfy Assumption B with $\mathbb E_{P_0}[M(\xi)^2]<\infty$, and suppose $\mathbb E_{P_0}[|\ell(x_0;\xi)|^2]<\infty$ for some $x_0\in\mathcal X$. Let $f$ satisfy Assumption A, let $\xi_1,\xi_2,\dots$ be i.i.d. with law $P_0$, and suppose the population optimizer $x^\star$ of $T_{\rm opt}(P)=\inf_{x\in\mathcal X}\mathbb E_P[\ell(x;\xi)]$ is unique with $\operatorname{Var}_{P_0}(\ell(x^\star;\xi))>0$. For $\rho\ge 0$, the lower endpoint of the empirical likelihood interval satisfies
--
--   $$P\Big(T_{\rm opt}(P_0)\ \ge\ \inf\Big\{T_{\rm opt}(P): D_f(P\,\|\,\widehat P_n)\le \tfrac{\rho}{n}\Big\}\Big)\ \longrightarrow\ P\big(N(0,1)\le\sqrt\rho\big).$$
--
--   Here the infimum runs over probability weight vectors $p$ on the $n$ sample points with $\frac1n\sum_i f(np_i)\le\rho/n$, and $T_{\rm opt}(p)=\inf_{x\in\mathcal X}\sum_i p_i\,\ell(x;\xi_i)$. This is the lower counterpart of the one-sided limit $P(T_{\rm opt}(P_0)\le\sup\{\cdots\})\to P(N(0,1)\ge-\sqrt\rho)$; together the two give Theorem 3.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, Appendix B.4 (proof of Theorem 10), p. 37: "By an exactly symmetric argument on -T(P0), we similarly have P(T(P0) >= inf_{P: D_f(P||P_n) <= rho/n} T(P)) -> P(N(0,1) <= sqrt rho)"; specialized to T_opt via Appendix C.1 (proof of Theorem 3).

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

/-- The lower one-sided coverage limit in Appendix B.4, p. 37: by the argument symmetric to the
upper one-sided limit, the probability that the lower endpoint inf {T_opt(P) : D_f(P||P̂_n) ≤ ρ/n}
lies below T_opt(P₀) converges to P(N(0,1) ≤ √ρ). -/
theorem one_sided_limit_lower
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
      sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) '' divergenceBall f ρ n) ≤
        optimalValue X ℓ (μ.map (ξ 0))})
      atTop (𝓝 (gaussianReal 0 1 (Set.Iic (Real.sqrt ρ)))) := by sorry

end GenEmpLik.Coverage
