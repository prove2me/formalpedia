-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_6
-- name    : IntroDelayAMDP.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:53:43.270211+00:00
-- url     : https://prove2.me/theorems/4f0c0d07-6c46-44df-baf1-4d40ec73d104
-- title:
--   Lemma A.6 — finishing probability of an attempt
-- statement:
--   For $C$ large enough and an estimate $(k,s,a)$ with $s\in\mathcal S_h$ that attempts with episode $\kappa$, let $\bar\alpha_{k,\kappa}(s,a)=\mathbf 1[(s_{\kappa,h},a_{\kappa,h})=(s,a)]\alpha_{k,\kappa}$. Then:
--
--   1. $\alpha_{k,\kappa}\le e^{1/4}/2$;
--   2. $\mathbb E[\bar\alpha_{k,\kappa}(s,a)\mid\mathcal F_{\kappa-1}]=q^{\pi_k}(s,a)/2$;
--   3. given $\mathcal F_{\kappa-1}$ and the trajectory $\tau_\kappa$, the indicators $I_{k,\kappa}(s,a)$ are independent across estimates with
--   $$\Pr(I_{k,\kappa}(s,a)=1\mid\mathcal F_{\kappa-1},\tau_\kappa)=\gamma+(1-\gamma)\bar\alpha_{k,\kappa}(s,a).$$
--
--   So every attempt finishes its estimate with probability $p_k(s,a)$, regardless of the history.
--
--   Differences from the source:
--   - encoding: an estimate that attempts with episode κ → each claim on the event that the deterministic key (k, s, a) is unfinished at the start of κ; reason: this event is F_{κ−1}-measurable
--   - encoding: the indicators are independent given F_{κ−1} and τ_κ → the conditional product formula for every finite set of keys and every pattern of values; reason: the definition of conditional independence for 0-1 variables
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - encoding: episodes k = 1, …, K → 0-based episodes k < K; reason: Lean convention; same instances
--   - encoding: terminal layer S_H → no terminal layer: last-layer rows vanish and V, B are 0 beyond the last layer; reason: the paper merges S_H into one state, which affects neither q_k nor B_k (p.30)
--   - encoding: the agent's and the environment's randomness → a run of Algorithm 1 as a function of a uniform random tape; reason: one realization of the protocol; the statement depends only on the joint law of the run
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.6, p.33

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_IsTransition
import Definitions.Def_IntroDelayAMDP_tabParams
import Definitions.Def_IntroDelayAMDP_tapeMeasure
import Definitions.Def_IntroDelayAMDP_tapeFilt
import Definitions.Def_IntroDelayAMDP_runState
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1Traj
import Definitions.Def_IntroDelayAMDP_alg1Ind
import Definitions.Def_IntroDelayAMDP_accProb
import Definitions.Def_IntroDelayAMDP_occ

namespace IntroDelayAMDP

open MeasureTheory

open Classical in
/-- **Lemma A.6 (Finishing Probability of an Attempt)** (printed p.33, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "For an estimate
`(k, s, a)` with `s ∈ S_h` that attempts with episode `κ`, let `ᾱ_{k,κ}(s, a) ≜ 1[(s_{κ,h}, a_{κ,h}) = (s, a)]α_{k,κ}`.
Then `α_{k,κ} ≤ e^{1/4}/2`, `E[ᾱ_{k,κ}(s, a) | F_{κ−1}] = q^{π_k}(s, a)/2`, and, given `F_{κ−1}` and the
trajectory `τ_κ` of episode `κ`, the indicators `I_{k,κ}(s, a)` are independent across estimates with
`Pr(I_{k,κ}(s, a) = 1 | F_{κ−1}, τ_κ) = γ + (1 − γ)ᾱ_{k,κ}(s, a)`. (34)"

For `C` large enough and Algorithm 1 with `tabParams C 0 S A H K δ`, for every 0-based episode `κ < K`:
1. on the event `att(k, s, a, κ)` that the estimate `(k, s, a)` is unfinished at the start of `κ`,
   `α_{k,κ} ≤ e^{1/4}/2`, where `α_{k,κ}` is (4) along `τ_κ` up to layer `h = layer(s)`;
2. `E[1_{att} ᾱ_{k,κ}(s, a) | F] = 1_{att} q^{π_k}(s, a)/2` a.s., with `F = tapeFilt … κ` (the paper's
   `F_{κ−1}`);
3. for every finite set `J` of keys and every `b ∈ {0, 1}^J`, on the event that all of `J` attempt,
   `Pr(I_i = b_i ∀ i ∈ J | F, τ_κ) = ∏_{i∈J} (γ + (1 − γ)ᾱ_i if b_i = 1, else 1 − γ − (1 − γ)ᾱ_i)` a.s.

**Formalization Note.** "Attempts with episode `κ`" is unfinished at the start of `κ`, an
`F`-measurable event, so each claim is stated on that event. The σ-algebra of `F_{κ−1}` and `τ_κ` is
`tapeFilt … κ ⊔ σ(τ_κ)`. Independence is the product formula for every finite `J`. -/
theorem lemma_A_6 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀,
      ∀ (St A : Type) [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] (H K : ℕ)
      (L : LayeredSpace St H) (P : St → A → St → ℝ), IsTransition L P →
      ∀ ℓ : ℕ → St → A → ℝ, (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1) →
      ∀ δ : ℝ, 0 < δ → δ < 1 → 1 ≤ K →
      let p := tabParams C 0 (Fintype.card St) (Fintype.card A) H K δ
      let μ := tapeMeasure St A K H
      let att : ℕ → St → A → ℕ → Set (Tape St A K H) :=
        fun k s a κ => {ω | (runState L P ℓ p ω κ).active k s a}
      let α : ℕ → St → ℕ → Tape St A K H → ℝ := fun k s κ ω =>
        accProb (alg1Policy L P ℓ p ω k) (alg1Policy L P ℓ p ω κ)
          (fun i : Fin (L.layer s + 1) => alg1Traj L P ℓ p ω κ i)
      let αb : ℕ → St → A → ℕ → Tape St A K H → ℝ := fun k s a κ ω =>
        (if alg1Traj L P ℓ p ω κ (L.layer s) = (s, a) then 1 else 0) * α k s κ ω
      ∀ κ < K,
        (∀ k s a, ∀ ω ∈ att k s a κ, α k s κ ω ≤ Real.exp (1 / 4) / 2) ∧
        (∀ k s a, μ[(att k s a κ).indicator (αb k s a κ) | tapeFilt St A K H κ] =ᵐ[μ]
          (att k s a κ).indicator (fun ω => occ L P (alg1Policy L P ℓ p ω k) s a / 2)) ∧
        (∀ (J : Finset (ℕ × St × A)) (b : ℕ × St × A → Bool),
          μ[(⋂ i ∈ J, att i.1 i.2.1 i.2.2 κ).indicator (fun ω => ∏ i ∈ J,
              if (alg1Ind L P ℓ p ω i.1 κ i.2.1 i.2.2 ↔ b i = true) then (1 : ℝ) else 0) |
            tapeFilt St A K H κ ⊔
              MeasurableSpace.comap (fun ω => alg1Traj L P ℓ p ω κ) (⊤ : MeasurableSpace (ℕ → St × A))]
          =ᵐ[μ] (⋂ i ∈ J, att i.1 i.2.1 i.2.2 κ).indicator (fun ω => ∏ i ∈ J,
              if b i = true then p.gamma + (1 - p.gamma) * αb i.1 i.2.1 i.2.2 κ ω
              else 1 - (p.gamma + (1 - p.gamma) * αb i.1 i.2.1 i.2.2 κ ω))) := by sorry

end IntroDelayAMDP
