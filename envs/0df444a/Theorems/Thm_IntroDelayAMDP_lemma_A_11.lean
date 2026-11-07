-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_11
-- name    : IntroDelayAMDP.lemma_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:58:37.412583+00:00
-- url     : https://prove2.me/theorems/683f9ccc-5761-4d86-902e-72f7aabffb7c
-- title:
--   Lemma A.11 — bounding Reg-Term
-- statement:
--   For $C$ large enough there is an absolute $c>0$ such that for every fixed comparator $\pi^\star$, with probability at least $1-\delta/16$, conditional on the good event $G$,
--   $$\text{Reg-Term}\le\frac{H\log A}\eta+2\eta H^5K+\frac12\sum_{k=1}^K\sum_sq^\star(s)b^{(1)}_k(s)+c\Bigl(\frac1\eta+H\Bigr).$$
--   This is the regret of exponential weights on the estimates $\hat Q_k-B_k$, including the delay cost of receiving the pieces over several episodes.
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
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.11, p.39

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_goodEvent
import Definitions.Def_IntroDelayAMDP_regTerm
import Definitions.Def_IntroDelayAMDP_bonus1
import Definitions.Def_IntroDelayAMDP_alg1QLow
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.11 (Bounding Reg-Term)** (printed p.39, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "With probability at least `1 − δ/16`,
conditional on the good event `G` of Lemma A.1, we have
`Reg-Term ≤ H log A/η + 2ηH⁵K + ½∑_{k=1}^K ∑_s q⋆(s)b^{(1)}_k(s) + O(1/η + H)`."

For `C` large enough there is an absolute `c > 0` such that, for Algorithm 1 with
`tabParams C 0 S A H K δ` and every fixed comparator `π⋆`, the probability that `G` holds and
`Reg-Term > H log A/η + 2ηH⁵K + ½∑_k∑_s q⋆(s)b^{(1)}_k(s) + c(1/η + H)` is at most `δ/16`.

**Formalization Note.** "Conditional on `G`" is read as intersection with `G` (as in Lemma A.9). -/
theorem lemma_A_11 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ),
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      ∀ πstar : St → A → ℝ, IsPolicy πstar →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      tapeMeasure St A K H (goodEvent K L P ℓ p (K - 1) ∩
        {ω | (H : ℝ) * Real.log (Fintype.card A) / p.eta + 2 * p.eta * (H : ℝ) ^ 5 * K +
            1 / 2 * ∑ k ∈ Finset.range K, ∑ s, occS L P πstar s *
              bonus1 p.c1 p.eta p.theta H (alg1Policy L P ℓ p ω k) (alg1QLow L P ℓ p ω k) s +
            c * (1 / p.eta + H) < regTerm L P ℓ p ω πstar}) ≤ ENNReal.ofReal (δ / 16) := by sorry

end IntroDelayAMDP
