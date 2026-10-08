-- Prove2me | Theorems.Thm_InfoGen_Gibbs_corollary_2
-- name    : InfoGen.Gibbs.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:40.157016+00:00
-- url     : https://prove2.me/theorems/dc2715e2-9416-41ce-b531-b9f937f58e77
-- title:
--   Corollary 2, p. 7 — expected excess population risk of Gibbs learning
-- statement:
--   Let $\mathcal W$ be countable, let $S$ contain $n\ge1$ independent examples from $\mu$, and let the jointly measurable loss $\ell(w,z)$ lie in $[0,1]$. For a probability prior $Q$ and $\beta>0$, suppose $w_o$ attains the smallest population risk and $Q(\{w_o\})>0$. The Gibbs output $W$ satisfies
--   $$\mathbb E[L_\mu(W)]\le\inf_{w\in\mathcal W}L_\mu(w)+\frac1\beta\log\frac1{Q(\{w_o\})}+\frac\beta{2n}.$$
--   Thus the expected excess risk depends on the prior's mass at a population-risk minimizer and the inverse sample size.
--
--   **Formalization Note** The minimizer and its positive prior mass are explicit: the printed statement names a minimizing $w_o$, while zero prior mass makes its logarithmic term infinite. Positive sample size and joint measurability make the expectations meaningful. Countable $\mathcal W$ is taken with measurable singletons, so that $Q(w_o)=Q(\{w_o\})$ is the prior mass of a point. The infimum remains over the entire hypothesis space as printed.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Corollary 2 and eq. (29), p. 7; proof App. D, p. 13

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

open LearnStability.Characterization (sampleLaw risk empRisk)

/-- Corollary 2 and (29), PDF p. 7. -/
theorem corollary_2 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0 : ℝ) 1)
    (Q : Measure W) [IsProbabilityMeasure Q]
    (β : ℝ) (hβ : 0 < β) (wo : W)
    (hwo : ∀ w, risk ℓ μ wo ≤ risk ℓ μ w)
    (hQ : Q {wo} ≠ 0) :
    (∫ p, risk ℓ μ p.2 ∂(sampleLaw μ n ⊗ₘ gibbsKernel ℓ Q β)) ≤
      (⨅ w, risk ℓ μ w) + 1 / β * Real.log (1 / (Q {wo}).toReal) +
        β / (2 * (n : ℝ)) := by sorry

end InfoGen.Gibbs
