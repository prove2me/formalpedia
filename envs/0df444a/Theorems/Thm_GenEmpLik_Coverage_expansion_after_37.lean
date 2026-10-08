-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_expansion_after_37
-- name    : GenEmpLik.Coverage.expansion_after_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:48:34.920601+00:00
-- url     : https://prove2.me/theorems/b1c135db-211e-41ed-b757-e410e1603ef9
-- title:
--   Appendix B.4 — expansion after (37)
-- statement:
--   Under the conditions of Theorem 3, write $U_{n,\rho}=\sup_{p\in\mathcal P_{n,\rho}}T_{\rm opt}(p)$, and let $\overline T_n^{(1)}$ and $s_n^2(T^{(1)})$ be the empirical mean and variance of the influence-function observations. Then
--
--   $$\left|\sqrt n\{U_{n,\rho}-T_{\rm opt}(P_0)\}-\sqrt n\,\overline T_n^{(1)}-\sqrt{\rho s_n^2(T^{(1)})}\right|\xrightarrow{P^*}0.$$
--
--   This is the one-sided asymptotic expansion used to calibrate the confidence region.
--
--   **Formalization Note** Convergence in outer probability is expanded to the probabilities of events where the absolute error exceeds each positive threshold.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 37, Appendix B.4, proof of Theorem 10, display after (37)

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

/-- The stochastic expansion in Appendix B.4 after (37), p. 37, for T_opt. -/
theorem expansion_after_37
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
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => μ {ω |
        δ < |Real.sqrt (n : ℝ) *
            (robustUpper X ℓ f ρ (fun i : Fin n => ξ i ω) -
              optimalValue X ℓ (μ.map (ξ 0))) -
          Real.sqrt (n : ℝ) *
            VarianceRegularization.Expansion.empMean
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)) -
          Real.sqrt (ρ * VarianceRegularization.Expansion.empVar
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)))|}) atTop (𝓝 0) := by sorry

end GenEmpLik.Coverage
