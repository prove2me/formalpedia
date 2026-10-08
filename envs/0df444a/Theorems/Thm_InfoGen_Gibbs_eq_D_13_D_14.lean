-- Prove2me | Theorems.Thm_InfoGen_Gibbs_eq_D_13_D_14
-- name    : InfoGen.Gibbs.eq_D_13_D_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:59.501909+00:00
-- url     : https://prove2.me/theorems/9fb0cbc1-45e2-4f55-bae5-13037136a86d
-- title:
--   Appendix D, (D.13)–(D.14), p. 13 — empirical risk comparison
-- statement:
--   Let $P^*_{W|S}$ be the Gibbs algorithm for a loss in $[0,1]$, a probability prior $Q$, and $\beta>0$. For any hypothesis $w$ with finite $D(\delta_w\Vert Q)$, write $D_*=D(P^*_{W|S}\Vert Q\mid P_S)$. Then
--   $$\mathbb E[L_S(W)]\le\mathbb E[L_S(W)]+\frac{D_*}{\beta}\le\mathbb E[L_S(w)]+\frac{D(\delta_w\Vert Q)}{\beta}.$$
--   The conditional divergence $D_*$ is finite. This comparison is the optimization step used in the excess risk bound.
--
--   **Formalization Note** The paper's standing nonnegative loss is strengthened here to its $[0,1]$ hypothesis from Corollary 2; this ensures that the real-valued divergences in the display are finite. Joint measurability and $n>0$ are explicit. The finite divergence of $\delta_w$ excludes the Lean conversion of $+\infty$ to zero.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, App. D, eqs. (D.13)–(D.14), p. 13

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

open LearnStability.Characterization (sampleLaw risk empRisk)

/-- The two inequalities (D.13)–(D.14), with the conditional KL cost finite. -/
theorem eq_D_13_D_14 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0 : ℝ) 1)
    (Q : Measure W) [IsProbabilityMeasure Q]
    (β : ℝ) (hβ : 0 < β) (w : W)
    (hw : klDiv (Measure.dirac w) Q ≠ ⊤) :
    let J := sampleLaw μ n ⊗ₘ gibbsKernel ℓ Q β
    let D := ∫⁻ s, klDiv (gibbsKernel ℓ Q β s) Q ∂(sampleLaw μ n)
    (∫ p, empRisk ℓ p.1 p.2 ∂J) ≤
      (∫ p, empRisk ℓ p.1 p.2 ∂J) + 1 / β * D.toReal ∧
    (∫ p, empRisk ℓ p.1 p.2 ∂J) + 1 / β * D.toReal ≤
      (∫ s, empRisk ℓ s w ∂(sampleLaw μ n)) +
        1 / β * (klDiv (Measure.dirac w) Q).toReal ∧
    D ≠ ⊤ := by sorry

end InfoGen.Gibbs
