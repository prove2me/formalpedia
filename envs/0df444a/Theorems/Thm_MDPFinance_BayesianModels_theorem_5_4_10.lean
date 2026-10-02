-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_theorem_5_4_10
-- name    : MDPFinance.BayesianModels.theorem_5_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:59.6792+00:00
-- url     : https://prove2.me/theorems/1f6133f1-e75f-42f1-8f3c-09827e0be2f0
-- title:
--   Theorem 5.4.10 — the Structure Assumption for the monotone information-based model
-- statement:
--   **Theorem 5.4.10** (the mission's goal). Suppose an information-based Markov Decision
--   Model with an upper bounding function $b$ is given, and:
--
--   (i) $D(\cdot)$ is increasing: $x \le x'$ implies $D(x) \subseteq D(x')$;
--   (ii) $q_Z(\cdot\mid\theta,a) \le_{lr} q_Z(\cdot\mid\theta',a)$ for all $\theta \le \theta'$,
--   $a \in A$;
--   (iii) $(x,z) \mapsto T^X(x,a,z)$ is increasing for every $a \in D(x)$;
--   (iv) $(\theta,x) \mapsto r(\theta,x,a)$ is increasing for every $a \in D(x)$;
--   (v) $(\theta,x) \mapsto g(\theta,x)$ is increasing;
--   (vi) every increasing $v \in IB_b^+$ has a maximizer in a given set $\Delta$.
--
--   Then $IM := \{v \in IB_b^+ \mid v \text{ increasing}\}$ and $\Delta$ satisfy the Structure
--   Assumption (SAN).
--
--   Together with Theorem 5.4.8, this is what turns "more favorable information state gives a more
--   aggressive/valuable optimal action" from an intuition into a theorem: it verifies, from
--   primitive, checkable hypotheses on the original Bayesian Model's ingredients ($D$, $q_Z$, $T^X$,
--   $r$, $g$), that the Bellman equation holds *and* that the value function and an optimal policy
--   are monotone in the information state — the structural fact both bandit theorems (5.5.1, 5.5.2)
--   of this mission specialize.
--
--   **Formalization Note.** This mission's disposition table treats this as a `draft`, not a
--   `kind: reference` to Chapter 2's general increasing-model theorem (this book's own Theorem
--   2.4.14, formalized in chunk `02c`): the content here is specifically that *this* model (built
--   from a sufficient statistic's information state, with its own likelihood-ratio-order-induced
--   order on $I$) satisfies that general theorem's hypotheses, which is genuine, model-specific work,
--   not a restatement of the general theorem itself. A formalization that merely assumed $\hat\Phi$
--   monotone (rather than deriving it, via Lemma 5.4.9, from the checkable hypothesis (ii) on
--   $q_Z$) would trivialize the theorem's actual content; this statement keeps (ii) as the
--   hypothesis, matching the book.
--
--   **Moderation note.** As in Lemma 5.4.9: the order on $I$ is the likelihood ratio order of the measures (`LRMeasure`), and the hypothesis `hPhihat_bayes` (the information-state update is the Bayes update wherever the latter is defined) is the step on which the book's proof rests; the upper bounding function uses a Lebesgue integral and $[-\infty,\infty]$-valued rewards.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 165, Theorem 5.4.10

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_InfoModel
import Definitions.Def_MDPFinance_BayesianModels_Operators
import Definitions.Def_MDPFinance_BayesianModels_StructureAssumption
import Definitions.Def_MDPFinance_BayesianModels_BoundingFunction
import Definitions.Def_MDPFinance_BayesianModels_Orders

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

/-- **Theorem 5.4.10** (Bäuerle–Rieder, p. 165, PDF 178, the goal theorem of this mission).
Suppose an information-based Markov Decision Model with an upper bounding function `b` is given
and (i) `D(\cdot)` is increasing, i.e. `x ≤ x'` implies `D(x) ⊂ D(x')`, (ii) `q_Z(\cdot|θ,a) ≤_{lr}
q_Z(\cdot|θ',a)` for all `θ ≤ θ'` and `a ∈ A`, (iii) `(x,z) ↦ T^X(x,a,z)` is increasing for all
`a ∈ D(x)`, (iv) `(θ,x) ↦ r(θ,x,a)` is increasing for all `a ∈ D(x)`, (v) `(θ,x) ↦ g(θ,x)` is
increasing, (vi) for all increasing `v ∈ IB_b^+` there exists a maximizer `f ∈ Δ` of `v`. Then the
sets `IM := \{v ∈ IB_b^+ \mid v \text{ increasing}\}` and `Δ` satisfy the Structure Assumption
(SAN). Standing simplifications of the "Monotonicity Results" subsection (p. 164, PDF 177) as in
`lemma_5_4_9`: `Θ, Z ⊆ ℝ`; `q_Z` independent of `x` (`qZbar`/`hqZ`); `μ̂` has a `Q_0`-density
`\hat p(θ|i)` (`phat`/`hphat`); the order on `I` is `i ≤ i' :⇔ \hat μ(\cdot|i) ≤_{lr}
\hat μ(\cdot|i')` in the sense of Definition B.3.5 (`hI_order` via `LRMeasure`); and, as in
Lemma 5.4.9, the information-state update `Φ̂` is the Bayes update of `\hat μ(\cdot|i)` wherever
the latter is defined (`hPhihat_bayes`, the step "by definition" in the proof of Lemma 5.4.9 on
which this theorem's proof rests). -/
theorem theorem_5_4_10 {EX A I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace I] [Preorder EX] [Preorder I] [Nonempty A]
    (M : BayesModel EX ℝ A ℝ) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → ℝ → I) (hSeq : S.IsSequential Phihat) (Im : InfoModel M Pf S Phihat)
    (qZbar : ℝ → A → ℝ → ℝ) (hqZ : ∀ x θ a z, M.qZ x θ a z = qZbar θ a z) (phat : I → ℝ → ℝ)
    (hphat : ∀ i, S.muHat i = M.Q0.withDensity fun θ => ENNReal.ofReal (phat i θ))
    (hI_order : ∀ i i' : I, i ≤ i' ↔ LRMeasure M.Q0 (S.muHat i) (S.muHat i'))
    (hPhihat_bayes : ∀ x i a z,
      0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
      (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
      ∀ C : Set ℝ, MeasurableSet C →
        S.muHat (Phihat x i a z) C =
          (∫⁻ θ in C, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) /
            (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)))
    (b : EX × I → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) b cr cg αb)
    (Δ : Set (EX × I → A))
    -- (i) D(·) is increasing.
    (hD_incr : ∀ x x' : EX, x ≤ x' → M.Dx x ⊆ M.Dx x')
    -- (ii) q_Z(·|θ,a) ≤_lr q_Z(·|θ',a) for all θ ≤ θ' and a ∈ A.
    (hqZ_lr : ∀ θ θ' a, θ ≤ θ' → LikelihoodRatioOrder (qZbar θ a) (qZbar θ' a))
    -- (iii) (x,z) ↦ T^X(x,a,z) is increasing for all a ∈ D(x).
    (hTX_incr : ∀ a, MonotoneOn (fun p : EX × ℝ => M.TX p.1 a p.2) {p | a ∈ M.Dx p.1})
    -- (iv) (θ,x) ↦ r(θ,x,a) is increasing for all a ∈ D(x).
    (hr_incr : ∀ a, MonotoneOn (fun p : ℝ × EX => M.r (p.2, p.1, a)) {p | a ∈ M.Dx p.2})
    -- (v) (θ,x) ↦ g(θ,x) is increasing.
    (hg_incr : Monotone fun p : ℝ × EX => M.g (p.2, p.1))
    -- (vi) every increasing v ∈ IB_b^+ has a maximizer in Δ.
    (hmax : ∀ v : EX × I → EReal, Monotone v → v ∈ IBbPlus b →
      ∃ f ∈ Δ, IsMaximizerOf (InfoD M) (fun ea => Im.Qhat ea)
        (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) M.β v f) :
    StructureAssumptionOf (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) M.β
      {v : EX × I → EReal | v ∈ IBbPlus b ∧ Monotone v} Δ := by sorry

end MDPFinance.BayesianModels
