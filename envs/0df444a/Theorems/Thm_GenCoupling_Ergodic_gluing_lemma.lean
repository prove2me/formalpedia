-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_gluing_lemma
-- name    : GenCoupling.Ergodic.gluing_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:51.661343+00:00
-- url     : https://prove2.me/theorems/acea8e46-2cdd-4475-ab45-3f5adedebf58
-- title:
--   Proof of Theorem 2.3(i), p. 8 — gluing lemma: couplings of (µ₁,µ₂) and (µ₂,µ₃) are marginals of one law on E³
-- statement:
--   Let $E$ be a Polish space and $\mu_1,\mu_2,\mu_3$ Borel probability measures on $E$. If $\gamma_1\in\mathcal C(\mu_1,\mu_2)$ and $\gamma_2\in\mathcal C(\mu_2,\mu_3)$, then there is a probability measure $\pi$ on $E\times E\times E$ whose $(1,2)$-marginal is $\gamma_1$ and whose $(2,3)$-marginal is $\gamma_2$:
--   $$\pi\circ(p_1,p_2)^{-1}=\gamma_1,\qquad \pi\circ(p_2,p_3)^{-1}=\gamma_2.$$
--
--   In the proof of Theorem 2.3(i) this puts the maximal coupling $(\hat Y,Z)$ and the generalized coupling $(X^{x,y}_t,Y^{x,y}_t)$ on one probability space with $\hat Y=Y^{x,y}_t$, so that $(X^{x,y}_t,Z)$ is a true coupling of $P_t(x,\cdot)$ and $P_t(y,\cdot)$ (cited there as [25, Lemma 4.3.2] and [43, p. 23]).
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, proof of Theorem 2.3(i), "By the gluing lemma (see, e.g., [25, Lemma 4.3.2] and [43, p. 23])"

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Gluing lemma (proof of Theorem 2.3(i), p. 8): couplings `γ₁ ∈ C(μ₁, μ₂)` and
`γ₂ ∈ C(μ₂, μ₃)` sharing the marginal `μ₂` are the two-dimensional marginals of one probability
measure on `E × E × E`. -/
theorem gluing_lemma {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ₁ μ₂ μ₃ : Measure E) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ₃]
    (γ₁ γ₂ : Measure (E × E)) (h₁ : γ₁ ∈ couplings μ₁ μ₂) (h₂ : γ₂ ∈ couplings μ₂ μ₃) :
    ∃ π : Measure (E × E × E), IsProbabilityMeasure π ∧
      π.map (fun p => (p.1, p.2.1)) = γ₁ ∧ π.map (fun p => (p.2.1, p.2.2)) = γ₂ := by sorry

end GenCoupling.Ergodic
