-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_half_S_eq_integral_score
-- name    : MultivarScores.LevelSet.half_S_eq_integral_score
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:54.000276+00:00
-- url     : https://prove2.me/theorems/5b7b4759-7521-4d05-8600-3303dae61436
-- title:
--   Theorem 2 “Moreover” (p. 13), (17) (p. 33) — ½S′(P_X, y; w, h) = ∫₀^∞ (S′)^Γ(L(f_X ∗ w; α), y; w, h, α) dα
-- statement:
--   Let $P_X$ be a probability measure on $\mathbb R^d$ (a forecast distribution), let $w,h:\mathbb R^d\to\mathbb R$ be measurable with $w\ge0$, $h\ge0$ and $h$ integrable, and assume $s\mapsto w(z-s)$ is $P_X$-integrable for almost every $z$, so that $f_X*w$ is well defined almost everywhere. Fix a realization $y\in\mathbb R^d$ and assume that $z\mapsto (f_X*w)^2(z)h(z)$ and $z\mapsto (f_X*w)(z)w(z-y)h(z)$ are integrable, so that $S'(P_X,y;w,h)$ in (3) is finite. Then
--
--   $$\tfrac12\,S'(P_X,y;w,h)=\int_0^\infty (S')^\Gamma\bigl(L(f_X*w;\alpha),y;w,h,\alpha\bigr)\,d\alpha .$$
--
--   This is the "Moreover" sentence of Theorem 2, proved as display (17) by applying the layer cake representation to both terms of (3). It exhibits the $L^2$ scoring rule as an integral over $\alpha$ of level set scores, generalizing the decomposition of the CRPS as twice the integral of quantile scores (10).
--
--   **Formalization Note** The $\alpha$-integral is the Bochner integral over $(0,\infty)$; under the stated hypotheses its integrand $\alpha\,\lambda(L_\alpha)-\mu_{y,w}(L_\alpha)$ is integrable. The integrability of $(f_X*w)^2h$ and $(f_X*w)w(\cdot-y)h$ is Assumption 1(b)/(c) for this $y$; the almost-everywhere integrability of $w(z-\cdot)$ is Assumption 1(a)'s requirement that $f_X*w$ be well defined (where it fails, the Lean value of $f_X*w$ would be $0$). The paper allows $w$ to be a local Borel measure (Assumption 1(a)); here $w$ is a measurable function, a disclosed specialization that excludes only the Dirac kernel $w=\delta_0$ (the density level set score (12)).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 13, Theorem 2 ("Moreover" sentence); p. 33, display (17)

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem half_S_eq_integral_score {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (PX : Measure (MultivarScores.L2Rule.E d))
    [IsProbabilityMeasure PX]
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (hwX : ∀ᵐ z, Integrable (fun s => w (z - s)) PX)
    (y : MultivarScores.L2Rule.E d)
    (hsq_int : Integrable (fun z => MultivarScores.L2Rule.smooth PX w z ^ 2 * h z))
    (hcross_int : Integrable (fun z => MultivarScores.L2Rule.smooth PX w z * w (z - y) * h z)) :
    (1 / 2 : ℝ) * MultivarScores.L2Rule.S' PX w h y = ∫ α in Set.Ioi (0 : ℝ), scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PX w) α) y := by sorry

end MultivarScores.LevelSet
