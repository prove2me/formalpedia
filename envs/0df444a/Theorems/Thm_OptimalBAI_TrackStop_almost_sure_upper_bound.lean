-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_almost_sure_upper_bound
-- name    : OptimalBAI.TrackStop.almost_sure_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:17:27.281468+00:00
-- url     : https://prove2.me/theorems/2db931e9-0b61-4292-b80f-5e206288d5b4
-- title:
--   Proposition 13 — almost-sure upper bound on the sample complexity of Chernoff's rule
-- statement:
--   Let $\boldsymbol\mu\in\mathcal S$ be an exponential family bandit model with $K\ge2$ arms, let $\alpha\in[1,e/2]$, and let $r:\mathbb N\to(0,\infty)$ satisfy $r(t)=O(t^\alpha)$. Let $\tau_\delta$ be Chernoff's stopping rule with $\beta(t,\delta)=\log(r(t)/\delta)$, and let the sampling rule be any rule ensuring that for every arm $a$, $N_a(t)/t$ converges almost surely to $w^*_a(\boldsymbol\mu)$. Then for all $\delta\in(0,1)$, $\mathbb P_{\boldsymbol\mu}(\tau_\delta<+\infty)=1$, and
--   $$\mathbb P_{\boldsymbol\mu}\left(\limsup_{\delta\to0}\frac{\tau_\delta}{\log(1/\delta)}\le\alpha\,T^*(\boldsymbol\mu)\right)=1,$$
--   where $T^*(\boldsymbol\mu)$ is the characteristic time of eq. (1).
--
--   This is the almost-sure counterpart of Theorem 14: it needs only the almost-sure convergence of the proportions, not a tracking rule.
--
--   **Formalization Note** $T^*(\boldsymbol\mu)$ is the platform's characteristic time of the class of exponential family models with a unique optimal arm (Kullback–Leibler divergences of the arm laws, values in $[0,\infty]$). The ratio $\tau_\delta/\log(1/\delta)$ is taken in $[0,\infty]$, with $\tau_\delta=\infty$ allowed. "$r(t)=O(t^\alpha)$" is written as $r(t)\le Dt^\alpha$ for all $t\ge1$ and some constant $D$; positivity of $r$ is added so that $\log(r(t)/\delta)$ is defined. Arm $a$ of the paper is index $a-1$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 11, Proposition 13 (§5.1)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_OptimalProportions
import Definitions.Def_OptimalBAI_TrackStop_ChernoffRule

open BanditAlgorithm Filter Topology ENNReal

namespace OptimalBAI.TrackStop

/-- Proposition 13 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 11). Let `μ` be an exponential
family bandit model in `𝒮` (parameters `θ ∈ 𝒮`), `α ∈ [1, e/2]` and `r(t) = O(t^α)`. Use Chernoff's
stopping rule `τ_δ` with `β(t, δ) = log(r(t)/δ)`, and any sampling rule `π` under which, almost
surely, `N_a(t)/t → w*_a(μ)` for every arm `a`. Then for all `δ ∈ (0, 1)`, `ℙ_μ(τ_δ < +∞) = 1`, and
almost surely `limsup_{δ → 0} τ_δ / log(1/δ) ≤ α T*(μ)`. -/
theorem almost_sure_upper_bound (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (θ : Fin K → F.Θ) (hθ : θ ∈ Sθ F K)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1 / 2))
    (r : ℕ → ℝ) (hr_pos : ∀ t, 0 < r t)
    (hr : ∃ D : ℝ, ∀ t : ℕ, 1 ≤ t → r t ≤ D * (t : ℝ) ^ α)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F (meanVec F θ) w)
    (π : BanditPolicy K)
    (hconv : ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π, ∀ a : Fin K,
      Tendsto (fun t : ℕ => (trajPullCount a t ω : ℝ) / (t : ℝ)) atTop (𝓝 (w a))) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,
      chernoffTime F (rateThreshold r δ) ω < ⊤) ∧
    ∀ᵐ ω ∂banditTrajMeasure (expFamilyBandit F θ) π,
      limsup (fun δ : ℝ => ((chernoffTime F (rateThreshold r δ) ω : ℝ≥0∞)) /
          ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal α * baiComplexity (expFamilyBandit F θ) (modelClass F K) := by sorry

end OptimalBAI.TrackStop
