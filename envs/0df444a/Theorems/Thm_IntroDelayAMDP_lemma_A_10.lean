-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_10
-- name    : IntroDelayAMDP.lemma_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:58:39.055555+00:00
-- url     : https://prove2.me/theorems/507fe761-a0b2-4c40-bc8e-fba30cb103bc
-- title:
--   Lemma A.10 — bounding Bias-2
-- statement:
--   For $C$ large enough there is an absolute $c>0$ such that for every fixed comparator $\pi^\star$, with probability at least $1-\delta/16$,
--   $$\text{Bias-2}\le c\,\frac{\nu\iota}\eta.$$
--   The overestimation of the estimates under $\pi^\star$ is controlled by the implicit exploration of the random stops.
--
--   Differences from the source:
--   - generalization: π⋆ the optimal policy in hindsight → every fixed comparator policy π⋆; reason: the proof never uses optimality; the optimal policy is one such comparator
--   - reading: Bias-2 = O(νι/η), for a signed quantity → the upper bound Bias-2 ≤ cνι/η; reason: the proof proves Bias-2 ≤ (2ν + 3)ι/η, and Theorem A.3 uses the upper bound only
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.10, p.38

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_IsPolicy
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_bias2

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.10 (Bounding Bias-2)** (printed p.38, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "With probability at least `1 − δ/16`,
we have `Bias-2 = O(νι/η)`."

For `C` large enough there is an absolute `c > 0` such that, for Algorithm 1 with
`tabParams C 0 S A H K δ` and every fixed comparator policy `π⋆`, `Pr(Bias-2 > cνι/η) ≤ δ/16`.

**Formalization Note.** "`Bias-2 = O(νι/η)`" is read as the upper bound `Bias-2 ≤ cνι/η` (the proof
proves `Bias-2 ≤ (2ν + 3)ι/η`). -/
theorem lemma_A_10 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ c > (0 : ℝ),
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      ∀ πstar : St → A → ℝ, IsPolicy πstar →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      tapeMeasure St A K H {ω | c * p.nu * p.iota / p.eta < bias2 L P ℓ p ω πstar} ≤
        ENNReal.ofReal (δ / 16) := by sorry

end IntroDelayAMDP
