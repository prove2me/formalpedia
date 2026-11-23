-- Prove2me | Theorems.Thm_MultiViewRedundancy_mu_approximation
-- name    : MultiViewRedundancy.mu_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:18:16.784577+00:00
-- url     : https://prove2.me/theorems/7f6de4f7-38b1-4476-8985-43352c9e71d2
-- title:
--   Lemma 1: the predictor $\mu$ through the other view
-- statement:
--   Let $(X,Z,Y)$ be random variables with $\mathbb E[Y^2]<\infty$, where $Z$ takes values in a standard Borel space. Let $\mu(x)=\mathbb E[\mathbb E[Y\mid Z]\mid X=x]$ and
--
--   $$\varepsilon_X=\mathbb E\big[(\mathbb E[Y\mid X]-\mathbb E[Y\mid X,Z])^2\big],\qquad \varepsilon_Z=\mathbb E\big[(\mathbb E[Y\mid Z]-\mathbb E[Y\mid X,Z])^2\big].$$
--
--   Then
--
--   $$\mathbb E\big[(\mu(X)-\mathbb E[Y\mid X,Z])^2\big]\le\varepsilon_X+2\sqrt{\varepsilon_X\varepsilon_Z}+\varepsilon_Z=\varepsilon_\mu.$$
--
--   When the views are redundant for predicting $Y$, predicting $Y$ through the other view $Z$ is nearly as good as the Bayes predictor that uses both views.
--
--   **Formalization Note** The law of $(X,Z,Y)$ is a probability measure on $\mathcal X\times\mathcal Z\times\mathbb R$. The finiteness of $\mathbb E[Y^2]$, which the paper uses implicitly so that $\varepsilon_X,\varepsilon_Z$ are finite, is a hypothesis.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 2.4, Lemma 1, p. 7; proof in Appendix A.1, p. 16

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem mu_approximation {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : MemLp (fun t => t.2.2) 2 ρ) :
    ∫ t, (muFn ρ t.1 - regXZ ρ t.1 t.2.1) ^ 2 ∂ρ ≤ epsMu ρ := by sorry

end MultiViewRedundancy
