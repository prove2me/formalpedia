-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_track_and_stop_asymptotic_optimality
-- name    : OptimalBAI.TrackStop.track_and_stop_asymptotic_optimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:18:15.411178+00:00
-- url     : https://prove2.me/theorems/78d178b3-62bb-480b-a8ce-04137f6015d1
-- title:
--   Theorem 14 — asymptotic optimality of Track-and-Stop
-- statement:
--   Let $\boldsymbol\mu\in\mathcal S$ be an exponential family bandit model with $K\ge2$ arms, let $\alpha\in[1,e/2]$, and let $r:\mathbb N\to(0,\infty)$ satisfy $r(t)=O(t^\alpha)$. Use Chernoff's stopping rule $\tau_\delta$ with $\beta(t,\delta)=\log(r(t)/\delta)$ and the sampling rule C-Tracking or D-Tracking. Then
--   $$\limsup_{\delta\to0}\frac{\mathbb E_{\boldsymbol\mu}[\tau_\delta]}{\log(1/\delta)}\le\alpha\,T^*(\boldsymbol\mu),$$
--   where $T^*(\boldsymbol\mu)$ is the characteristic time of eq. (1).
--
--   Combined with the lower bound $\mathbb E_{\boldsymbol\mu}[\tau_\delta]\ge T^*(\boldsymbol\mu)\,\mathrm{kl}(\delta,1-\delta)$ of Theorem 1 for $\delta$-PAC strategies, this shows that Track-and-Stop attains the optimal sample complexity as $\delta\to0$ (up to the factor $\alpha$, which can be taken equal to $1$).
--
--   **Formalization Note** The statement holds for every run of either tracking rule: for every target map with values in $\Sigma_K$ that returns the optimal proportions $w^*$ on $\mathcal S$ (the paper leaves $w^*(\hat{\boldsymbol\mu}(t))$ undefined when $\hat{\boldsymbol\mu}(t)\notin\mathcal S$), every choice of $L^\infty$ projections, and every tie-breaking. The expectation, the ratio and $T^*(\boldsymbol\mu)$ take values in $[0,\infty]$, so an infinite expectation is never read as $0$. $T^*(\boldsymbol\mu)$ is the platform's characteristic time of the class of exponential family models with a unique optimal arm. "$r(t)=O(t^\alpha)$" is written as $r(t)\le Dt^\alpha$ for all $t\ge1$ and some constant $D$; positivity of $r$ is added so that $\log(r(t)/\delta)$ is defined. "Let $\boldsymbol\mu$ be an exponential family bandit model" is read as $\boldsymbol\mu\in\mathcal S$, the class fixed on p. 4, on which $T^*$ and $w^*$ are defined.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 13, Theorem 14 (proof: App. D.1, pp. 27–29)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_Tracking
import Definitions.Def_OptimalBAI_TrackStop_ChernoffRule

open BanditAlgorithm Filter Topology ENNReal

namespace OptimalBAI.TrackStop

/-- Theorem 14 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 13): asymptotic optimality of
Track-and-Stop. Let `μ` be an exponential family bandit model in `𝒮` (parameters `θ ∈ 𝒮`),
`α ∈ [1, e/2]` and `r(t) = O(t^α)`. Use Chernoff's stopping rule `τ_δ` with
`β(t, δ) = log(r(t)/δ)`, and a sampling rule `π` that is a run of C-Tracking or of D-Tracking
(for any target map `wt` with values in `Σ_K` that returns the optimal proportions `w*` on `𝒮`,
any choice of projections, any tie-breaking). Then
`limsup_{δ → 0} 𝔼_μ[τ_δ] / log(1/δ) ≤ α T*(μ)`,
with the expectation and `T*(μ)` in `[0, ∞]`. -/
theorem track_and_stop_asymptotic_optimality (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1 / 2))
    (r : ℕ → ℝ) (hr_pos : ∀ t, 0 < r t)
    (hr : ∃ D : ℝ, ∀ t : ℕ, 1 ≤ t → r t ≤ D * (t : ℝ) ^ α)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    limsup (fun δ : ℝ =>
        (∫⁻ ω, (chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)
            ∂banditTrajMeasure (expFamilyBandit F θ) π) /
          ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] (0 : ℝ)) ≤
      ENNReal.ofReal α * baiComplexity (expFamilyBandit F θ) (modelClass F K) := by sorry

end OptimalBAI.TrackStop
