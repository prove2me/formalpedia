-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_one_sided_limit
-- name    : GenEmpLik.Coverage.one_sided_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:49:02.368824+00:00
-- url     : https://prove2.me/theorems/1b657e15-0de8-4b96-bea5-233055e8c2ef
-- title:
--   Appendix B.4 — one-sided coverage limit
-- statement:
--   Under the conditions of Theorem 3, the upper endpoint of the optimal-value image has the one-sided limit
--
--   $$P^*\!\left(T_{\rm opt}(P_0)\le U_{n,\rho}\right)\longrightarrow P\{Z\ge-\sqrt\rho\},\qquad Z\sim N(0,1).$$
--
--   This is one of the two symmetric tail statements used in the proof of exact coverage. It concerns $\sup_p T_{\rm opt}(p)$, rather than the separate minimax robust program.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 37, Appendix B.4, proof of Theorem 10, one-sided limit

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

/-- The one-sided coverage limit in Appendix B.4, p. 37. -/
theorem one_sided_limit
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
      optimalValue X ℓ (μ.map (ξ 0)) ≤
        robustUpper X ℓ f ρ (fun i : Fin n => ξ i ω)})
      atTop (𝓝 (gaussianReal 0 1 (Set.Ici (-(Real.sqrt ρ))))) := by sorry

end GenEmpLik.Coverage
