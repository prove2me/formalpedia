-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_tracking_converges_as
-- name    : OptimalBAI.TrackStop.tracking_converges_as
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:16:33.128168+00:00
-- url     : https://prove2.me/theorems/33b0251c-44bf-4a4c-9265-d2281f452e95
-- title:
--   Proposition 9 — tracking rules converge to the optimal proportions almost surely
-- statement:
--   Let $\boldsymbol\mu\in\mathcal S$ be an exponential family bandit model with $K\ge2$ arms and let $w^*(\boldsymbol\mu)$ be its optimal proportions. Let $w^*$ also denote a target map with values in $\Sigma_K$ that returns optimal proportions at every point of $\mathcal S$. For every policy that is a run of C-Tracking or of D-Tracking with this target, the number $N_a(t)$ of draws of arm $a$ in the first $t$ rounds satisfies, for every arm $a$,
--   $$\mathbb P_{\boldsymbol\mu}\left(\lim_{t\to\infty}\frac{N_a(t)}{t}=w^*_a(\boldsymbol\mu)\right)=1.$$
--
--   Almost-sure convergence of the empirical proportions is the only property of the sampling rule used by the almost-sure sample complexity bound (Proposition 13).
--
--   **Formalization Note** The paper prints $\mathbb P_w$; the probability is $\mathbb P_{\boldsymbol\mu}$, the law of the trajectory of the policy in the model $\boldsymbol\mu$. The event holds simultaneously for all arms. The paper's $w^*(\hat{\boldsymbol\mu}(t))$ is undefined when $\hat{\boldsymbol\mu}(t)\notin\mathcal S$; the statement holds for every way of filling this gap with a point of $\Sigma_K$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 8, Proposition 9 (proof: App. B.3)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_Tracking

open BanditAlgorithm Filter Topology

namespace OptimalBAI.TrackStop

/-- Proposition 9 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 8). Let `μ` be an exponential family
bandit model in `𝒮` (parameters `θ ∈ 𝒮`) and `w = w*(μ)` its optimal proportions. For every target
map `wt` with values in `Σ_K` that returns optimal proportions on `𝒮`, and every policy that is a
run of C-Tracking or of D-Tracking with that target, almost surely `N_a(t)/t → w_a` for every arm
`a`. (The printed `ℙ_w` is `ℙ_μ`.) -/
theorem tracking_converges_as (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F (meanVec F θ) w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ'))
    (π : BanditPolicy K) (hπ : IsCTrackingPolicy wt π ∨ IsDTrackingPolicy wt π) :
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ a : Fin K,
      Tendsto (fun t : ℕ => (trajPullCount a t ω : ℝ) / (t : ℝ)) atTop (𝓝 (w a)) := by sorry

end OptimalBAI.TrackStop
