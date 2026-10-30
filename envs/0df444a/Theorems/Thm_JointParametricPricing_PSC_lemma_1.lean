-- Prove2me | Theorems.Thm_JointParametricPricing_PSC_lemma_1
-- name    : JointParametricPricing.PSC.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:49:00.012077+00:00
-- url     : https://prove2.me/theorems/86c2b304-4f0a-4848-93a7-39561d9372fb
-- title:
--   Lemma 1 — exploration MLE tail and root-mean-square error
-- statement:
--   In the standing general parametric pricing model, suppose A5 holds for the fixed exploration prices. There are constants $\eta_1,\eta_2,\eta_3>0$, independent of the positive integer exploration length $L$ and of $\theta\in\Theta$, such that every maximizing MLE selector for the prescribed $L$-observation block schedule satisfies, for every $\delta>0$,
--   $$P_\theta^\pi(\|\theta-\widehat\theta_L\|_2>\delta)\le\eta_1 e^{-\eta_2 L\delta^2},\qquad \sqrt{E_\theta^\pi\|\theta-\widehat\theta_L\|_2^2}\le\frac{\eta_3}{\sqrt L}.$$
--   This is the pure exploration experiment, without conditioning on inventory survival. All positive lengths, including incomplete blocks and $L<\widetilde q$, are retained. Convexity of $\Theta$ and the well-separated assumption A7 are not imposed; the gap in the source's use of Theorem EC.1 is preserved (I3).
--
--   Differences from the source:
--   - encoding: positive finite dimensions, Euclidean norms, and parameters in Θ → Fin indices, EuclideanSpace vectors, and the subtype Θ; reason: preserves the full continuous domains and the source 2-norms
--   - encoding: C² or C¹ functions on the stated compact domains → local ambient smooth representatives at domain points, with coordinate derivatives; reason: implements the usual smooth-on-a-compact-domain convention without imposing global smoothness or any new uniform exterior bound
--   - encoding: any maximum-likelihood maximizer → a fixed selector over observation strings with its exact likelihood-maximization property; reason: keeps all ties and derives the probability from the actual experiment; no concentration property is assumed
--   - encoding: the exploration policy and its observation law → the exact categorical product likelihood with zero-based index floor(s qtilde/L), finite probability and mean-square sums; reason: a finite outcome space does not discretize the price box; the statistical experiment is the one specified in context
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Lemma 1, printed 12 / PDF 13

import Definitions.Def_JointParametricPricing_PSC_Exploration

namespace JointParametricPricing.PSC

theorem lemma_1 {n m q : ℕ} (M : Model n m q) (E : ExplorationPrices M) (hA5 : E.A5) :
    ∃ η₁ η₂ η₃ : ℝ, 0 < η₁ ∧ 0 < η₂ ∧ 0 < η₃ ∧ ∀ S : E.MLESelector,
      ∀ L : ℕ, 0 < L → ∀ θ : M.Θ,
        (∀ δ : ℝ, 0 < δ → E.tail S L θ δ ≤ η₁ * Real.exp (-η₂ * L * δ ^ 2)) ∧
        Real.sqrt (E.meanSquare S L θ) ≤ η₃ / Real.sqrt L := by sorry

end JointParametricPricing.PSC
