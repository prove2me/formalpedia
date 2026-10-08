-- Prove2me | Theorems.Thm_InfoGen_Gibbs_theorem_5
-- name    : InfoGen.Gibbs.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:43.544358+00:00
-- url     : https://prove2.me/theorems/8320ae58-f426-4078-962d-913370cf9d91
-- title:
--   Theorem 5, p. 6 — the Gibbs algorithm minimizes the relaxed objective
-- statement:
--   Let $S$ consist of $n\ge1$ independent samples from $\mu$, let $\ell$ be a nonnegative loss, let $Q$ be a probability distribution on hypotheses, and let $\beta>0$. The Gibbs rule is a Markov kernel, its distribution at every sample $s$ is the exponential tilt
--   $$P^*_{W|S=s}(dw)=\frac{e^{-\beta L_s(w)}Q(dw)}{\mathbb E_Q[e^{-\beta L_s(W)}]},$$
--   and it minimizes
--   $$\mathbb E[L_S(W)]+\frac1\beta D(P_{W|S}\Vert Q\mid P_S)$$
--   over all Markov learning kernels. Moreover, for each sample $s$ the Gibbs distribution is the unique solution of the samplewise problem (C.12): any probability measure $P$ on hypotheses with
--   $$\mathbb E_P[L_s(W)]+\frac1\beta D(P\Vert Q)\le\mathbb E_{P^*_{W|S=s}}[L_s(W)]+\frac1\beta D(P^*_{W|S=s}\Vert Q)$$
--   equals $P^*_{W|S=s}$. The result identifies the samplewise Gibbs rule as the solution of the paper's relaxed learning problem.
--
--   **Formalization Note** Joint measurability of the loss and a positive sample size make the displayed random quantities meaningful; the paper leaves them implicit. "The solution" is rendered as optimality over all Markov kernels together with uniqueness of the minimizer for each sample, the form in which Appendix C (p. 13) solves (C.12); kernel-level uniqueness is stated samplewise, which avoids measurability questions about $s\mapsto D(P_{W|S=s}\Vert Q)$ for an arbitrary kernel. The objective is extended nonnegative, preserving infinite costs.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Theorem 5 and eqs. (26)–(27), p. 6; proof App. C, p. 13

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

open LearnStability.Characterization (sampleLaw risk empRisk)

/-- Theorem 5, (26)–(27), PDF p. 6. The last conjunct is "the solution" of (C.12), App. C,
p. 13: for each sample `s`, the Gibbs distribution is the only probability measure on `W` whose
samplewise objective is at most the Gibbs value. -/
theorem theorem_5 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (Q : Measure W) [IsProbabilityMeasure Q]
    (β : ℝ) (hβ : 0 < β) :
    IsMarkovKernel (gibbsKernel (n := n) ℓ Q β) ∧
    (∀ s : Fin n → Z, gibbsKernel ℓ Q β s = Q.tilted (fun w => -β * empRisk ℓ s w)) ∧
    (∀ κ : Kernel (Fin n → Z) W, IsMarkovKernel κ →
      relaxedObjective ℓ μ Q β (gibbsKernel (n := n) ℓ Q β) ≤
        relaxedObjective ℓ μ Q β κ) ∧
    (∀ s : Fin n → Z, ∀ P : Measure W, IsProbabilityMeasure P →
      (∫⁻ w, ENNReal.ofReal (empRisk ℓ s w) ∂P) + ENNReal.ofReal (1 / β) * klDiv P Q ≤
        (∫⁻ w, ENNReal.ofReal (empRisk ℓ s w) ∂(gibbsKernel ℓ Q β s)) +
          ENNReal.ofReal (1 / β) * klDiv (gibbsKernel ℓ Q β s) Q →
      P = gibbsKernel ℓ Q β s) := by sorry

end InfoGen.Gibbs
