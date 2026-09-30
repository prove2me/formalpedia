-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_d_tracking_bounds
-- name    : OptimalBAI.TrackStop.d_tracking_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:15:57.220152+00:00
-- url     : https://prove2.me/theorems/7860e4e9-ebaa-4b8d-a0b6-83fba5a1deeb
-- title:
--   Lemma 8 — D-Tracking guarantees
-- statement:
--   Let $\boldsymbol\mu\in\mathcal S$ be the mean vector of an exponential family bandit model and $w^*(\boldsymbol\mu)$ its optimal proportions. Let $w^*$ also denote a target map with values in $\Sigma_K$ that returns optimal proportions at every point of $\mathcal S$. Consider a trajectory whose arms follow the D-Tracking rule with this target, and let $N_a(t)$ be the number of draws of arm $a$ in the first $t$ rounds and $\hat{\boldsymbol\mu}(t)$ the empirical means. Then:
--
--   1. for every $t$ and every arm $a$, $N_a(t)\ge(\sqrt t-K/2)_+-1$;
--   2. for all $\epsilon>0$ and all $t_0$, there exists $t_\epsilon\ge t_0$, depending only on $\epsilon$ and $t_0$ (not on the trajectory), such that for every trajectory following the rule
--   $$\sup_{t\ge t_0}\max_a\big|w^*_a(\hat{\boldsymbol\mu}(t))-w^*_a(\boldsymbol\mu)\big|\le\epsilon\quad\Rightarrow\quad\sup_{t\ge t_\epsilon}\max_a\Big|\frac{N_a(t)}{t}-w^*_a(\boldsymbol\mu)\Big|\le3(K-1)\epsilon.$$
--
--   Forced exploration makes every arm grow like $\sqrt t$, and once the plug-in targets settle near $w^*(\boldsymbol\mu)$ the empirical proportions follow them.
--
--   **Formalization Note** The statement is pathwise, for every trajectory that follows the rule with any tie-breaking; $t_\epsilon$ is chosen before the trajectory, as the paper's remark after Lemma 17 (p. 22, "the constant $n_1$ in Lemma 17 depends on $\epsilon$, hence the notation $t_\epsilon$") and its use in Lemma 20 (p. 28) require. $K\ge2$ is assumed, as throughout the paper's analysis ($\mathcal S$ and $\mathrm{Alt}$ need two arms).
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 7, Lemma 8 (proof via Lemma 17, App. B.2, p. 22)

import Mathlib
import Definitions.Def_OptimalBAI_TrackStop_Tracking

open BanditAlgorithm

namespace OptimalBAI.TrackStop

/-- Lemma 8 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 7). Let `μ ∈ 𝒮` with optimal proportions
`w = w*(μ)`, and let `wt` be a target map with values in `Σ_K` that returns optimal proportions on
`𝒮`. Along any trajectory that follows D-Tracking with target `wt`,
`N_a(t) ≥ (√t - K/2)_+ - 1` for every `t` and `a`. Moreover, for all `ε > 0` and all `t₀` there is
`t_ε ≥ t₀`, the same for every trajectory (the paper, p. 22: "the constant `n₁` in Lemma 17 depends
on `ε`, hence the notation `t_ε`"), such that along any trajectory that follows D-Tracking, if
`max_a |w*_a(μ̂(t)) - w_a| ≤ ε` for every `t ≥ t₀`, then `max_a |N_a(t)/t - w_a| ≤ 3(K-1)ε` for
every `t ≥ t_ε`. -/
theorem d_tracking_bounds (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ')) :
    (∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω → ∀ (t : ℕ) (a : Fin K),
      max (Real.sqrt (t : ℝ) - (K : ℝ) / 2) 0 - 1 ≤ (trajPullCount a t ω : ℝ)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℕ, ∃ tε : ℕ, t₀ ≤ tε ∧
      ∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω →
        ((∀ t : ℕ, t₀ ≤ t → ∀ a : Fin K, |wt (trajMeanVec t ω) a - w a| ≤ ε) →
          ∀ t : ℕ, tε ≤ t → ∀ a : Fin K,
            |(trajPullCount a t ω : ℝ) / (t : ℝ) - w a| ≤ 3 * ((K : ℝ) - 1) * ε) := by sorry

end OptimalBAI.TrackStop
