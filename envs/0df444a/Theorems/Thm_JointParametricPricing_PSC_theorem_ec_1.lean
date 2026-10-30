-- Prove2me | Theorems.Thm_JointParametricPricing_PSC_theorem_ec_1
-- name    : JointParametricPricing.PSC.theorem_ec_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:47:16.50041+00:00
-- url     : https://prove2.me/theorems/6ab2c056-9c09-4373-a90e-7c3239edfaa2
-- title:
--   Theorem EC.1 — uniform exponential tail for the IID MLE
-- statement:
--   Let $\Theta\subseteq\mathbb R^q$ be nonempty, compact, and convex, with $q\ge1$, and let $\{P_\theta:\theta\in\Theta\}$ be a family of distributions on a discrete sample space $Y$. Assume identifiability, a uniformly finite $r$-moment of the Euclidean log score for some $r>q$, differentiability of $\sqrt{P_\theta(y)}$ within $\Theta$ at every parameter for each outcome, and positive-definite Fisher information with entries $E_\theta[-\partial_i\partial_j\log P_\theta(Y)]$. These derivatives and finite expectations are interpreted on statistical support. For any likelihood-maximizing selector based on $t$ IID samples, there are $\eta_1,\eta_2>0$ depending only on the family, $\Theta,r,q$, such that uniformly over $\theta\in\Theta$, integers $t\ge1$, and $\delta\ge0$,
--   $$P_\theta(\|\widehat\theta(t)-\theta\|_2>\delta)\le\eta_1\exp(-t\eta_2\delta^2).$$
--   The sample space may be infinite. The statement is attributed to the held paper's Theorem EC.1, which quotes Borovkov; no original-book page is asserted.
--
--   Differences from the source:
--   - encoding: positive finite dimensions, Euclidean norms, and parameters in Θ → Fin indices, EuclideanSpace vectors, and the subtype Θ; reason: preserves the full continuous domains and the source 2-norms
--   - reading: θ⊆Θ in the printed family → θ∈Θ; reason: θ is a parameter vector, as in the theorem and likelihood maximization
--   - encoding: IID probability and finite score/Fisher expectations → mass functions, extended-nonnegative sums for events and score moments, and summable real Fisher entries; reason: avoids any default value for a divergent expectation; a finite uniform moment bound is equivalent to a finite supremum
--   - encoding: parameter derivatives on Θ and log scores of random outcomes → square-root masses differentiable within Θ, with genuine ambient log gradients and second coordinate derivatives required only on positive statistical support; reason: retains boundary points where a square-root mass has only a derivative within Θ, and interprets log derivatives on statistical support without demanding positive probability of impossible outcomes
--   - encoding: any maximum-likelihood maximizer → a fixed selector over observation strings with its exact likelihood-maximization property; reason: keeps all ties and derives the probability from the actual experiment; no concentration property is assumed
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); Theorem EC.1, printed ec1 / PDF 25

import Definitions.Def_JointParametricPricing_PSC_DiscreteStatistics

namespace JointParametricPricing.PSC

theorem theorem_ec_1 {q : ℕ} {Y : Type*} (F : DiscreteFamily q Y) (r : ℝ)
    (h : F.Regular r) :
    ∃ η₁ η₂ : ℝ, 0 < η₁ ∧ 0 < η₂ ∧ ∀ S : F.MLESelector,
      ∀ θ : F.Θ, ∀ t : ℕ, 1 ≤ t → ∀ δ : ℝ, 0 ≤ δ →
        F.tail S t θ δ ≤ ENNReal.ofReal (η₁ * Real.exp (-(t : ℝ) * η₂ * δ ^ 2)) := by sorry

end JointParametricPricing.PSC
