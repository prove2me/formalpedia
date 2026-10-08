-- Prove2me | Theorems.Thm_InfoGen_Gibbs_gibbs_gen_bound
-- name    : InfoGen.Gibbs.gibbs_gen_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:18.240961+00:00
-- url     : https://prove2.me/theorems/17e7e4af-20a1-4a35-b47a-35e4709d1f16
-- title:
--   Equation (28), p. 7 — Gibbs generalization error is at most β/(2n)
-- statement:
--   For a jointly measurable loss $\ell$ taking values in $[0,1]$, a sample of size $n\ge1$, a probability prior $Q$, and $\beta>0$, the Gibbs learning algorithm satisfies
--   $$|\operatorname{gen}(\mu,P^*_{W|S})|\le\frac{\beta}{2n}.$$
--   This sharp generalization estimate is the second ingredient in the population risk guarantee.
--
--   **Formalization Note** Xu and Raginsky quote this estimate from Raginsky et al. (2016), rather than proving it in this paper. Joint measurability of the loss and positive sample size are explicit; the paper leaves them implicit.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, eq. (28), p. 7, attributed there to Raginsky et al. 2016 [13]

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

/-- Equation (28), quoted from Raginsky et al. (2016), PDF p. 7. -/
theorem gibbs_gen_bound {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0 : ℝ) 1)
    (Q : Measure W) [IsProbabilityMeasure Q]
    (β : ℝ) (hβ : 0 < β) :
    |InfoGen.Expected.genError ℓ μ (gibbsKernel (n := n) ℓ Q β)| ≤ β / (2 * (n : ℝ)) := by sorry

end InfoGen.Gibbs
