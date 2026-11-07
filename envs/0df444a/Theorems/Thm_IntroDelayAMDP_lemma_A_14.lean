-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_14
-- name    : IntroDelayAMDP.lemma_A_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:54:23.610385+00:00
-- url     : https://prove2.me/theorems/32ac4e7c-7dd9-4edb-ae1d-e41acc27ca0f
-- title:
--   Lemma A.14 — harmonic visit counts
-- statement:
--   For $C$ large enough, with probability at least $1-\delta/32$,
--   $$\sum_{k=1}^K\sum_{s,a}\frac{q^{\pi_k}(s,a)}{\max\{1,N_k(s,a)\}}\le2SA(2+\log K)+2H\iota.$$
--   It bounds the inverse visit counts in Lemma A.13, summed over the episodes.
--
--   Differences from the source:
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.14, p.43

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_eventA14

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.14 (Harmonic Visit Counts)** (printed p.43, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "With probability at least `1 − δ/32`,
we have `∑_{k=1}^K ∑_{s,a} q^{π_k}(s, a)/max{1, N_k(s, a)} ≤ 2SA(2 + log K) + 2Hι`."

For `C` large enough and Algorithm 1 with `tabParams C 0 S A H K δ`, the complement of `eventA14` (the
displayed inequality, natural logarithm) has probability at most `δ/32`. -/
theorem lemma_A_14 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      tapeMeasure St A K H (eventA14 K L P ℓ p)ᶜ ≤ ENNReal.ofReal (δ / 32) := by sorry

end IntroDelayAMDP
