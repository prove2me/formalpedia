-- Prove2me | Theorems.Thm_OptimalBAI_LowerBound_sample_complexity_lower_bound
-- name    : OptimalBAI.LowerBound.sample_complexity_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:52:50.99164+00:00
-- url     : https://prove2.me/theorems/9795f814-627f-4fe1-bcca-a7f285bf3d13
-- title:
--   Theorem 1 — non-asymptotic lower bound on the sample complexity of $\delta$-PAC strategies
-- statement:
--   Fix a canonical one-parameter exponential family and $K$ arms. Let $\mathcal S$ be any set of bandit models of the family each of which has a unique optimal arm $a^*(\boldsymbol\mu)$, and for $\boldsymbol\mu \in \mathcal S$ let
--
--   $$\mathrm{Alt}(\boldsymbol\mu) = \{\boldsymbol\lambda \in \mathcal S : a^*(\boldsymbol\lambda) \ne a^*(\boldsymbol\mu)\}, \qquad \Sigma_K = \Big\{w \in \mathbb R_+^K : \sum_{a=1}^K w_a = 1\Big\}.$$
--
--   The **characteristic time** $T^*(\boldsymbol\mu) \in [0, \infty]$ is defined by
--
--   $$T^*(\boldsymbol\mu)^{-1} = \sup_{w \in \Sigma_K}\ \inf_{\boldsymbol\lambda \in \mathrm{Alt}(\boldsymbol\mu)} \sum_{a=1}^K w_a\, d(\mu_a, \lambda_a),$$
--
--   with $d(\mu_a, \lambda_a)$ the Kullback–Leibler divergence between the reward laws of arm $a$ under $\boldsymbol\mu$ and $\boldsymbol\lambda$ (so $T^* = 0$ when $\mathrm{Alt}(\boldsymbol\mu)$ is empty and $T^* = \infty$ when the supremum is $0$).
--
--   **Theorem.** Let $\delta \in (0, 1/2]$. For every strategy $(\pi, \tau, \psi)$ that is $\delta$-PAC on $\mathcal S$ — $\tau$ a stopping time of the natural filtration, $\psi$ an $\mathcal F_\tau$-measurable decision — and every $\boldsymbol\mu \in \mathcal S$,
--
--   $$\mathbb E_{\boldsymbol\mu}[\tau] \ \ge\ T^*(\boldsymbol\mu)\, \mathrm{kl}(\delta, 1 - \delta),$$
--
--   where $\mathrm{kl}(x, y) = x \log\frac{x}{y} + (1 - x)\log\frac{1 - x}{1 - y}$.
--
--   This is the paper's lower bound: it holds for every $\delta$, not only asymptotically, and its constant $T^*(\boldsymbol\mu)$ is the one matched by the Track-and-Stop strategy as $\delta \to 0$. Since $\mathrm{kl}(\delta, 1 - \delta) \sim \log(1/\delta)$, it gives $\liminf_{\delta \to 0} \mathbb E_{\boldsymbol\mu}[\tau_\delta]/\log(1/\delta) \ge T^*(\boldsymbol\mu)$.
--
--   **Formalization Note** The paper states $\delta \in (0, 1)$; the claim is false for $\delta \in (1/2, 1)$ (a one-draw strategy deciding on the fractional part of a Gaussian reward is $0.9$-PAC while $T^*(\boldsymbol\mu) \to \infty$ as the two means merge), so $\delta \le 1/2$ is assumed; at $\delta = 1/2$ the bound is $0$. $T^*$ is the platform's `baiComplexity` over the class $\{\text{models of } \mathcal S\}$, and $\mathbb E_{\boldsymbol\mu}[\tau]$ is a lower integral, both in $[0, \infty]$. The platform's alternative set uses disjoint optimal-arm sets, which for models with a unique optimal arm is $a^*(\boldsymbol\lambda) \ne a^*(\boldsymbol\mu)$. Arms are 0-based in Lean.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 3, Theorem 1 (with the definition of $T^*$, eq. (1), on p. 4)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_OptimalBAI_LowerBound_ExpFamily
import Definitions.Def_OptimalBAI_LowerBound_IsDeltaPAC

open MeasureTheory ENNReal BanditAlgorithm

namespace OptimalBAI.LowerBound

/-- Theorem 1 of Garivier–Kaufmann (arXiv:1602.04589v2, p. 3, with eq. (1) on p. 4), for
`δ ∈ (0, 1/2]`. Let `𝒮` be any set of exponential-family bandit models each of which has a unique
optimal arm. For every `δ`-PAC strategy `(π, τ, ψ)` on `𝒮` and every `μ ∈ 𝒮`,
`E_μ[τ] ≥ T*(μ) · kl(δ, 1 - δ)`, where `T*(μ)` is the characteristic time of eq. (1)
(`baiComplexity`, with `d = KL` of the arm laws).

Printed slip handled: the paper states `δ ∈ (0, 1)`; the statement is false for `δ ∈ (1/2, 1)`
(its proof uses `kl(1-δ, δ) ≥ kl(δ, 1-δ)`-monotonicity valid only for `δ ≤ 1/2`), so `δ ≤ 1/2`
is assumed. Arms are 0-based. Expectations and `T*` are in `ℝ≥0∞`. -/
theorem sample_complexity_lower_bound {K : ℕ} (F : ExpFamily) (S : Set (Fin K → F.Θ))
    (hS : ∀ θ ∈ S, ∃ a, F.IsBestArm θ a)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (π : BanditPolicy K) (τ : (ℕ → Fin K × ℝ) → ℕ∞) (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hPAC : IsDeltaPAC δ π τ ψ (expFamilyBandit F '' S))
    (θ : Fin K → F.Θ) (hθ : θ ∈ S) :
    baiComplexity (expFamilyBandit F θ) (expFamilyBandit F '' S) *
        ENNReal.ofReal (bernoulliRelativeEntropy δ (1 - δ)) ≤
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure (expFamilyBandit F θ) π := by sorry

end OptimalBAI.LowerBound
