-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_lemma_16
-- name    : GenEmpLik.Coverage.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:48:47.815441+00:00
-- url     : https://prove2.me/theorems/63633ab6-5c01-4fa9-8764-3fec1d81132a
-- title:
--   Lemma 16 — uniform negligible remainder
-- statement:
--   Under Assumptions A and B, the square moment, i.i.d. sample, unique optimizer, and positive influence variance conditions of Theorem 3, let $\kappa(p)$ be the linearization remainder. For every $\varepsilon>0$,
--
--   $$\limsup_{n\to\infty}P^*\!\left(\sup_{p:D_f(p\|\widehat P_n)\le\rho/n}|\kappa(p)|\ge\frac{\varepsilon}{\sqrt n}\right)=0.$$
--
--   This uniform estimate transfers the empirical influence-function expansion to the nonlinear optimal-value functional.
--
--   **Formalization Note** $P^*$ is the outer probability of the displayed event. The general Donsker hypotheses of Theorem 10 are supplied here by the concrete compact Lipschitz loss class.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 37, Lemma 16, Eq. (37), specialized to T_opt

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

/-- Lemma 16, p. 37, specialized to the optimal-value functional. -/
theorem lemma_16
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
    ∀ ε : ℝ, 0 < ε →
      Filter.limsup (fun n : ℕ => μ {ω |
        ε / Real.sqrt (n : ℝ) ≤
          sSup ((fun p => |remainder X ℓ (μ.map (ξ 0))
            (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
            (fun i : Fin n => ξ i ω) p|) '' divergenceBall f ρ n)})
        atTop = 0 := by sorry

end GenEmpLik.Coverage
