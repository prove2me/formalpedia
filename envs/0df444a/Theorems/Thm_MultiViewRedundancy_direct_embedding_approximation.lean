-- Prove2me | Theorems.Thm_MultiViewRedundancy_direct_embedding_approximation
-- name    : MultiViewRedundancy.direct_embedding_approximation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:20:27.887906+00:00
-- url     : https://prove2.me/theorems/9a898075-319b-49e9-8b75-6da5675b834a
-- title:
--   Lemma 6: approximating $g^\star$ by inner products suffices
-- statement:
--   Let $(X,Z,Y)$ have $\mathbb E[Y^2]<\infty$, $Z$ valued in a standard Borel space and $p_{X,Z}\ll p_X\otimes p_Z$. For all measurable $\eta:\mathcal X\to\mathbb R^m$ and $\psi:\mathcal Z\to\mathbb R^m$ there is $w\in\mathbb R^m$ with
--
--   $$\mathbb E\big[(w^\top\eta(X)-\mu(X))^2\big]\le\mathbb E[Y^2]\cdot\varepsilon_{\mathrm{direct}}(\eta,\psi),\qquad \varepsilon_{\mathrm{direct}}(\eta,\psi)=\mathbb E\big[(\eta(X)^\top\psi(\tilde Z)-g^\star(X,\tilde Z))^2\big],$$
--
--   where $(X,\tilde Z)\sim p_X\otimes p_Z$.
--
--   So it suffices to find embeddings whose inner product approximates $g^\star$ under the product of the marginals.
--
--   **Formalization Note** Both sides take values in $[0,\infty]$, so the statement also covers $\varepsilon_{\mathrm{direct}}=\infty$. Measurability of $\eta,\psi$, finiteness of $\mathbb E[Y^2]$ and $p_{X,Z}\ll p_X\otimes p_Z$ are the paper's standing conventions, stated as hypotheses.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 4.2, Lemma 6, p. 11; proof in Appendix A.5, p. 18

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem direct_embedding_approximation {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : MemLp (fun t => t.2.2) 2 ρ)
    (hac : lawXZ ρ ≪ (lawXZ ρ).fst.prod (lawXZ ρ).snd)
    {m : ℕ} (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ) (hη : Measurable η) (hψ : Measurable ψ) :
    ∃ w : Fin m → ℝ,
      ∫⁻ x, ENNReal.ofReal ((∑ i, w i * η x i - muFn ρ x) ^ 2) ∂(lawXZ ρ).fst ≤
        ENNReal.ofReal (∫ t, t.2.2 ^ 2 ∂ρ) * epsDirect (lawXZ ρ) η ψ := by sorry

end MultiViewRedundancy
