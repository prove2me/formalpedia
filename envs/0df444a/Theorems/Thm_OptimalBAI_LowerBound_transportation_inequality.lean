-- Prove2me | Theorems.Thm_OptimalBAI_LowerBound_transportation_inequality
-- name    : OptimalBAI.LowerBound.transportation_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:46:53.967769+00:00
-- url     : https://prove2.me/theorems/1866f3e6-0dcc-4ce6-ae7f-b69f6246c83d
-- title:
--   Eq. (2) — transportation inequality for $\delta$-PAC strategies
-- statement:
--   Fix a canonical one-parameter exponential family and $K$ arms. Let $\mathcal S$ be a set of bandit models of the family, each of which has a unique optimal arm, and let $\delta \in (0, 1/2]$. Consider a strategy $(\pi, \tau, \psi)$ — $\tau$ a stopping time of the natural filtration and $\psi$ an $\mathcal F_\tau$-measurable decision — that is $\delta$-PAC on $\mathcal S$. For a model $\boldsymbol\mu \in \mathcal S$ write $\mathbb E_{\boldsymbol\mu}$ for the expectation under the law of the trajectory it generates, and $N_a(t)$ for the number of draws of arm $a$ among the first $t$ rounds.
--
--   Then for every $\boldsymbol\mu \in \mathcal S$ and every $\boldsymbol\lambda \in \mathcal S$ whose optimal arm differs from that of $\boldsymbol\mu$,
--
--   $$\sum_{a=1}^K d(\mu_a, \lambda_a)\, \mathbb E_{\boldsymbol\mu}\big[N_a(\tau)\big] \ \ge\ \mathrm{kl}(\delta, 1 - \delta),$$
--
--   where $d(\mu_a, \lambda_a)$ is the Kullback–Leibler divergence between the reward laws of arm $a$ under the two models and $\mathrm{kl}(x, y) = x \log\frac{x}{y} + (1 - x) \log\frac{1 - x}{1 - y}$ is the binary relative entropy.
--
--   This is the "transportation" inequality (Lemma 1 of Kaufmann, Cappé and Garivier, 2015) on which the proof of Theorem 1 rests: any strategy that distinguishes $\boldsymbol\mu$ from $\boldsymbol\lambda$ with error at most $\delta$ must collect, in expectation, at least $\mathrm{kl}(\delta, 1 - \delta)$ nats of information.
--
--   **Formalization Note** The paper states the inequality for $\delta \in (0, 1)$; it is false for $\delta \in (1/2, 1)$ (a strategy that draws arm 1 once and decides by the fractional part of the reward is $0.9$-PAC on unit-variance Gaussian models, while the left side can be arbitrarily small), so $\delta \le 1/2$ is assumed. Divergences and expectations are in $[0, \infty]$. $N_a(\tau)$ is read at $\tau$ truncated to $0$ where $\tau = \infty$; that event has probability zero under the $\delta$-PAC hypothesis. "Different optimal arms" is stated as: no arm is optimal for both models. Arms are 0-based in Lean.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 4, proof of Theorem 1, eq. (2) (Lemma 1 of Kaufmann, Cappé, Garivier 2015)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_TrackAndStop
import Definitions.Def_OptimalBAI_LowerBound_ExpFamily
import Definitions.Def_OptimalBAI_LowerBound_IsDeltaPAC

open MeasureTheory ENNReal InformationTheory BanditAlgorithm

namespace OptimalBAI.LowerBound

/-- Eq. (2) of Garivier–Kaufmann (arXiv:1602.04589v2, p. 4), the transportation inequality
(Lemma 1 of Kaufmann, Cappé, Garivier 2015), for `δ ∈ (0, 1/2]`. Let `𝒮` be any set of
exponential-family bandit models each with a unique optimal arm, `(π, τ, ψ)` a `δ`-PAC strategy on
`𝒮`, and `μ, λ ∈ 𝒮` with different optimal arms. Then
`∑_a d(μ_a, λ_a) E_μ[N_a(τ)] ≥ kl(δ, 1 - δ)`, with `d(μ_a, λ_a) = KL(ν_{θ_a}, ν_{θ'_a})` and
`N_a(τ)` the number of draws of arm `a` in the first `τ` rounds.

`(τ ω).toNat` is `0` when `τ ω = ⊤`; that event is null by the `δ`-PAC hypothesis. As in
Theorem 1, `δ ≤ 1/2` is added (false for `δ ∈ (1/2, 1)`). -/
theorem transportation_inequality {K : ℕ} (F : ExpFamily) (S : Set (Fin K → F.Θ))
    (hS : ∀ θ ∈ S, ∃ a, F.IsBestArm θ a)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ θ' : Fin K → F.Θ) (hθ : θ ∈ S) (hθ' : θ' ∈ S)
    (hdiff : ∀ a, F.IsBestArm θ a → ¬ F.IsBestArm θ' a) :
    ENNReal.ofReal (bernoulliRelativeEntropy δ (1 - δ)) ≤
      ∑ a, klDiv ((expFamilyBandit F θ).P a) ((expFamilyBandit F θ').P a) *
        ∫⁻ ω, (trajPullCount a (τ ω).toNat ω : ℝ≥0∞)
          ∂banditTrajMeasure (expFamilyBandit F θ) π := by sorry

end OptimalBAI.LowerBound
