-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_5
-- name    : IntroDelayAMDP.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:55.643222+00:00
-- url     : https://prove2.me/theorems/95a49a7d-7a33-4e48-84da-7cfb2317ec04
-- title:
--   Lemma A.5 — stability of nearby policies
-- statement:
--   For $C$ large enough, on every sample point of Algorithm 1 and for all episodes with $|\kappa-k|\le M+2\bar d$, every partial trajectory $(s_0,a_0,\dots,s_h,a_h)$ satisfies
--   $$e^{-1/4}\le\prod_{h'=0}^h\frac{\pi_k(a_{h'}\mid s_{h'})}{\pi_\kappa(a_{h'}\mid s_{h'})}\le e^{1/4}.$$
--   This shows the acceptance probability $\alpha_{k,\kappa}$ is at most 1 for all attempts.
--
--   Differences from the source:
--   - generalization: a partial trajectory (s₀, a₀, …, s_h, a_h) → any h + 1 state-action pairs, feasible or not; reason: the bound holds factor by factor in the proof
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - generalization: Algorithm 1 run with d̄ = 0 (the paper reuses the lemma with 1 ≤ d̄ ≤ K for the delayed Algorithm 4) → Algorithm 1 run with the parameters of any d̄ ≤ K; reason: the proof uses only (P2) and the per-update bound (33), which hold for these parameters; d̄ = 0 is the paper's Algorithm 1
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.5, p.32

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_Tape
import Definitions.Def_IntroDelayAMDP_alg1Policy

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.5 (Stability of Nearby Policies)** (printed p.32, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "If `|κ − k| ≤ M + 2d̄`, then every
partial trajectory `(s₀, a₀, …, s_h, a_h)` satisfies `e^{−1/4} ≤ ∏_{h′=0}^h π_k(a_{h′} | s_{h′})/π_κ(a_{h′} | s_{h′})
≤ e^{1/4}`. (31)"

For `C` large enough, every instance, losses in `[0, 1]`, `K ≥ 1`, `δ ∈ (0, 1)` and every delay cap
`d̄ ≤ K`, Algorithm 1 run with `tabParams C d̄ S A H K δ` satisfies, on every sample point, for all
0-based episodes `k, κ < K` with `|κ − k| ≤ M + 2d̄`, every `h < H` and every sequence of `h + 1`
state-action pairs, the two-sided bound (31).

**Formalization Note.** The pairs need not form a feasible trajectory (the bound is per factor). The
paper states the lemma for `d̄ = 0` (Algorithm 1) and reuses it with `1 ≤ d̄ ≤ K`; both are covered. -/
theorem lemma_A_5 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      ∀ dbar : ℕ, dbar ≤ K →
      let p := tabParams C dbar (Fintype.card St) (Fintype.card A) H K δ
      ∀ ω : Tape St A K H, ∀ k κ : ℕ, k < K → κ < K → ((k : ℤ) - κ).natAbs ≤ p.M + 2 * dbar →
      ∀ h < H, ∀ t : Fin (h + 1) → St × A,
        Real.exp (-(1 / 4)) ≤ ∏ i, alg1Policy L P ℓ p ω k (t i).1 (t i).2 /
            alg1Policy L P ℓ p ω κ (t i).1 (t i).2 ∧
          ∏ i, alg1Policy L P ℓ p ω k (t i).1 (t i).2 / alg1Policy L P ℓ p ω κ (t i).1 (t i).2 ≤
            Real.exp (1 / 4) := by sorry

end IntroDelayAMDP
