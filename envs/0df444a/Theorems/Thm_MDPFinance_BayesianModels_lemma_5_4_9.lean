-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_lemma_5_4_9
-- name    : MDPFinance.BayesianModels.lemma_5_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:02.692689+00:00
-- url     : https://prove2.me/theorems/ff8c3f81-39ac-4e2a-98aa-5e04b6447937
-- title:
--   Lemma 5.4.9 — MTP2 $\Leftrightarrow$ likelihood ratio order
-- statement:
--   **Lemma 5.4.9**, under the "Monotonicity Results" subsection's standing simplifications
--   ($Z,\Theta \subseteq \mathbb R$; $Q^Z$ independent of $x$ with density $q_Z(\cdot\mid\theta,a)$;
--   $\hat\mu$ has a $Q_0$-density $\hat p(\theta\mid i)$; the order on $I$ is $i \le i' :\Leftrightarrow
--   \hat\mu(\cdot\mid i) \le_{lr} \hat\mu(\cdot\mid i')$):
--
--   a) If $q_Z(z\mid\theta,a)$ is MTP2 in $(z,\theta)$ for every $a$, then $(i,z) \mapsto
--   \hat\Phi(x,i,a,z)$ is increasing for every $a \in A$ (and every $x$).
--
--   b) Fixing $a$: $q_Z(\cdot\mid\theta,a) \le_{lr} q_Z(\cdot\mid\theta',a)$ for all $\theta \le
--   \theta'$ if and only if $q_Z(z\mid\theta,a)$ is MTP2 in $(z,\theta)$.
--
--   Part b) gives a practically checkable sufficient condition (MTP2 of a joint density) for the
--   likelihood-ratio monotonicity hypothesis of the goal Theorem 5.4.10; part a) is the key
--   propagation step used in that theorem's own proof, showing the information-state update itself
--   inherits the monotonicity.
--
--   **Formalization Note.** MTP2 is a joint condition on $q_Z(z\mid\theta,a)$ as a function of the
--   *pair* $(z,\theta)$, not a property of $z$ or $\theta$ separately — getting the two-variable
--   quantification right (`IsMTP2` on `ℝ × ℝ`) is the entire content of part b).
--
--   **Moderation note.** The order on $I$ is the likelihood ratio order of the measures $\hat\mu(\cdot\mid i)$ (`LRMeasure`, Definition B.3.5). Part a) needs the step "by definition $\hat\mu(\cdot\mid\hat\Phi(i,a,z))=\Phi(\cdot\mid\hat\mu(\cdot\mid i),a,z)$" of the book's proof, which is now the hypothesis `hPhihat_bayes` (the information-state update is the Bayes update wherever the latter is defined; it holds at every reachable information state by sufficiency, sequentiality and the filter recursion), and it is stated at pairs $(i,z)\le(i',z')$ where both Bayes updates are defined. The draft asserted monotonicity of an unconstrained $\hat\Phi$ on all of $I\times Z$, with no link between $\hat\Phi$ and the sufficient statistic, which is refutable.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 163-164, Lemma 5.4.9

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_Orders

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- Lemma 5.4.9 (Bäuerle–Rieder, p. 163, PDF 177), under the "Monotonicity Results" standing
simplifications of that subsection (p. 164, PDF 177: `Z ⊂ ℝ`, `E_X ⊂ ℝ^d`, `Θ ⊂ ℝ`; `Q^Z(\cdot|
x,θ,a)` independent of `x` with density `q_Z(\cdot|θ,a)` w.r.t. a σ-finite measure — here `qZbar`,
with `hqZ` recording the `x`-independence of `M.qZ`; `μ̂` has a `Q_0`-density `\hat p(θ|i)` —
here `phat`, with `hphat`; the order on `I`, `i ≤ i' :⇔ \hat μ(\cdot|i) ≤_{lr} \hat μ(\cdot|i')`,
i.e. the likelihood ratio order of Definition B.3.5 on the measures `\hat μ(\cdot|i)`, `\hat
μ(\cdot|i')` — here `hI_order` via `LRMeasure`). The proof's step "by definition `\hat μ(\cdot|
\hat Φ(i,a,z)) = Φ(\cdot|\hat μ(\cdot|i),a,z)`" is the hypothesis `hPhihat_bayes`: the
information-state update is the Bayes update of `\hat μ(\cdot|i)` wherever the latter is defined
(normalizing constant positive and finite); it holds at every reachable information state by
`SuffStat.ht_suff`, `IsSequential` and `Posterior.hmu_rec`. a) If `q_Z(z|θ,a)` is an `MTP2`
function in `(z,θ)` for all `a`, then `(i,z) ↦ Φ̂(x,i,a,z)` is increasing for all `a ∈ A` (and
every `x`), at pairs where both Bayes updates are defined. b) Fix `a ∈ A`. We have
`q_Z(\cdot|θ,a) ≤_{lr} q_Z(\cdot|θ',a)` for all `θ ≤ θ'` if and only if `q_Z(z|θ,a)` is an `MTP2`
function in `(z,θ)`. -/
theorem lemma_5_4_9 {EX A I : Type*} [MeasurableSpace EX] [MeasurableSpace A] [MeasurableSpace I]
    [Preorder I] (M : BayesModel EX ℝ A ℝ) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → ℝ → I) (qZbar : ℝ → A → ℝ → ℝ)
    (hqZ : ∀ x θ a z, M.qZ x θ a z = qZbar θ a z) (phat : I → ℝ → ℝ)
    (hphat : ∀ i, S.muHat i = M.Q0.withDensity fun θ => ENNReal.ofReal (phat i θ))
    (hI_order : ∀ i i' : I, i ≤ i' ↔ LRMeasure M.Q0 (S.muHat i) (S.muHat i'))
    (hSeq : S.IsSequential Phihat)
    (hPhihat_bayes : ∀ x i a z,
      0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
      (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
      ∀ C : Set ℝ, MeasurableSet C →
        S.muHat (Phihat x i a z) C =
          (∫⁻ θ in C, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) /
            (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i))) :
    ((∀ a, IsMTP2 fun q : ℝ × ℝ => qZbar q.2 a q.1) →
        ∀ x a (i i' : I) (z z' : ℝ), i ≤ i' → z ≤ z' →
          0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
          (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
          0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z') ∂(S.muHat i')) →
          (∫⁻ θ, ENNReal.ofReal (qZbar θ a z') ∂(S.muHat i')) < ⊤ →
          Phihat x i a z ≤ Phihat x i' a z') ∧
      (∀ a, (∀ θ θ' : ℝ, θ ≤ θ' → LikelihoodRatioOrder (qZbar θ a) (qZbar θ' a)) ↔
        IsMTP2 fun q : ℝ × ℝ => qZbar q.2 a q.1) := by sorry

end MDPFinance.BayesianModels
