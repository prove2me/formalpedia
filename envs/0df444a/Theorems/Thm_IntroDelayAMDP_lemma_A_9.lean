-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_9
-- name    : IntroDelayAMDP.lemma_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:58:23.369721+00:00
-- url     : https://prove2.me/theorems/e3737c6f-f22a-4fa8-a729-f3ee6a377424
-- title:
--   Lemma A.9 — bounding Bias-1
-- statement:
--   For $C$ large enough there is an absolute $c>0$ such that for every fixed comparator $\pi^\star$, with probability at least $1-3\delta/32$, conditional on the good event $G$ and the event of Lemma A.7,
--   $$\text{Bias-1}\le\sum_{k=1}^K\sum_sq^\star(s)\Bigl(b^{(2)}_k(s)+\frac12b^{(1)}_k(s)\Bigr)+c\frac\iota\eta.$$
--   The bonus covers the underestimation of the estimates under $\pi_k$.
--
--   Differences from the source:
--   - generalization: π⋆ the optimal policy in hindsight → every fixed comparator policy π⋆; reason: the proof never uses optimality; the optimal policy is one such comparator
--   - reading: with probability at least 1 − p, conditional on the event E, X holds → μ(E ∩ {not X}) ≤ p; reason: this is how the proof of Theorem A.3 combines the lemmas by a union bound; a conditional probability would be a different claim
--   - reading: O(·) → ≤ c·(·) with c > 0 chosen after C and before the instance; reason: every O-constant is absolute given the universal C
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.9, p.36

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_goodEvent
import Definitions.Def_IntroDelayAMDP_eventA7
import Definitions.Def_IntroDelayAMDP_bias1
import Definitions.Def_IntroDelayAMDP_bonus1
import Definitions.Def_IntroDelayAMDP_bonus2
import Definitions.Def_IntroDelayAMDP_alg1QLow
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.9 (Bounding Bias-1)** (printed p.36, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "With probability at least `1 − 3δ/32`,
conditional on the good event `G` of Lemma A.1 and the event of Lemma A.7, we have
`Bias-1 ≤ ∑_{k=1}^K ∑_s q⋆(s)(b^{(2)}_k(s) + ½b^{(1)}_k(s)) + O(ι/η)`."

For `C` large enough there is an absolute `c > 0` such that, for Algorithm 1 with
`tabParams C 0 S A H K δ` and every fixed comparator policy `π⋆` (`q⋆ = q^{π⋆}`), the probability that
`G` and the event of Lemma A.7 hold and `Bias-1 > ∑_k ∑_s q⋆(s)(b^{(2)}_k(s) + ½b^{(1)}_k(s)) + cι/η` is
at most `3δ/32`.

**Formalization Note.** "With probability `≥ 1 − p`, conditional on `E`, we have `X`" is read as
`Pr(E ∩ {not X}) ≤ p`, the form in which the proof of Theorem A.3 combines the lemmas by a union bound. -/
theorem lemma_A_9 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ),
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      ∀ πstar : St → A → ℝ, IsPolicy πstar →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      tapeMeasure St A K H (goodEvent K L P ℓ p (K - 1) ∩ eventA7 K L P ℓ p ∩
        {ω | ∑ k ∈ Finset.range K, ∑ s, occS L P πstar s *
            (bonus2 p.theta H (alg1Policy L P ℓ p ω k) (alg1QLow L P ℓ p ω k) s +
              1 / 2 * bonus1 p.c1 p.eta p.theta H (alg1Policy L P ℓ p ω k) (alg1QLow L P ℓ p ω k) s)
            + c * p.iota / p.eta < bias1 L P ℓ p ω πstar}) ≤ ENNReal.ofReal (3 * δ / 32) := by sorry

end IntroDelayAMDP
