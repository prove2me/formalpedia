-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_7
-- name    : IntroDelayAMDP.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:55:39.614407+00:00
-- url     : https://prove2.me/theorems/5e2f5642-ff4a-406f-8443-17e23dae02ba
-- title:
--   Lemma A.7 — inactive caps
-- statement:
--   For $C$ large enough, with probability at least $1-\delta/8$, at the start of every episode $k$ with $G_k$, every pair has fewer than $\nu$ unfinished estimates, and every estimate $(k,s,a)$ started in an episode $k\le K-M$ with $G_k$ has $\sum_\kappa I_{k,\kappa}(s,a)=1$.
--
--   So, with high probability, neither the cap $M$ on attempts nor the cap $\nu$ on unfinished estimates binds.
--
--   Differences from the source:
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.7, p.33

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_eventA7

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.7 (Inactive Caps)** (printed p.33, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "With probability at least `1 − δ/8`, at the start of
every episode `k` with `G_k`, every pair has fewer than `ν` unfinished estimates, and every estimate
`(k, s, a)` started in an episode `k ≤ K − M` with `G_k` has `∑_κ I_{k,κ}(s, a) = 1`."

For `C` large enough and Algorithm 1 with `tabParams C 0 S A H K δ`, the complement of the event
`eventA7` has probability at most `δ/8`. -/
theorem lemma_A_7 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      tapeMeasure St A K H (eventA7 K L P ℓ p)ᶜ ≤ ENNReal.ofReal (δ / 8) := by sorry

end IntroDelayAMDP
