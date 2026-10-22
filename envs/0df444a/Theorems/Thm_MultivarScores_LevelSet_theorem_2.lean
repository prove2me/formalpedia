-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_theorem_2
-- name    : MultivarScores.LevelSet.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:12.583362+00:00
-- url     : https://prove2.me/theorems/dda745e8-c8f6-46b1-9029-17326cb177ad
-- title:
--   Theorem 2, p. 13 — the level set score (S′)^Γ (11) is consistent for the α level set L(f_Y ∗ w; α)
-- statement:
--   Let $P_Y$ be a probability measure on $\mathbb R^d$, the distribution of the observation $Y$, with smoothed density $(f_Y*w)(z)=\int w(z-s)\,dP_Y(s)$. Let $w,h:\mathbb R^d\to\mathbb R$ be measurable, with $w\ge0$, $h\ge0$, $h$ integrable, and $(s,z)\mapsto w(z-s)h(z)$ integrable with respect to $P_Y\otimes\mathcal L^d$. Let $\alpha>0$ and let $A\subseteq\mathbb R^d$ be a Borel set. With the level set score
--
--   $$(S')^\Gamma(A,y;w,h,\alpha)=\int_{\mathbb R^d}\bigl(\alpha-w(z-y)\bigr)\mathbb 1\{z\in A\}h(z)\,dz \qquad (11)$$
--
--   and the $\alpha$ level set $L(f_Y*w;\alpha)=\{z : (f_Y*w)(z)\ge\alpha\}$ of (9),
--
--   $$\mathbb E_{P_Y}\bigl[(S')^\Gamma(L(f_Y*w;\alpha),\bullet;w,h,\alpha)\bigr]\le\mathbb E_{P_Y}\bigl[(S')^\Gamma(A,\bullet;w,h,\alpha)\bigr].$$
--
--   In words, (11) is a consistent scoring function for the $\alpha$ level set of $f_Y*w$: no Borel set has a smaller expected score than the true level set. This is the first claim of Theorem 2; it gives the level set analogue of a proper scoring rule, with the CDF level set score (13) and the density level set score (12) as special cases.
--
--   **Formalization Note** The product-integrability hypothesis pins down Assumption 1 and Theorem 2's "$(S')^\Gamma(A,\bullet)$ is finite $\mathcal L^d$-a.e. and $(S')^\Gamma(A,\bullet)f_Y(\bullet)$ is integrable". With $w,h\ge0$, Tonelli bounds $\iint w(z-y)\mathbb 1_B(z)h(z)\,dz\,dP_Y(y)$ by $\iint w(z-y)h(z)\,dz\,dP_Y(y)$ for every Borel $B$ at once, including $L(f_Y*w;\alpha)$, for which the comparison also needs it, and $\lambda(B)\le\int h<\infty$ handles the $\alpha$-term. A single $P_Y$ replaces the class $\mathcal V^d$: the statement is pointwise in $P_Y$, and $\mathcal V^d$ enters only through Assumption 1. The paper allows $w$ to be a local Borel measure (Assumption 1(a)); here $w$ is a measurable function, a disclosed specialization that excludes only the Dirac kernel $w=\delta_0$ (the density level set score (12)).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 13, Theorem 2 (first two sentences), display (11); p. 12, (9) and the definition of consistency; p. 32, Assumption 1

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem theorem_2 {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d => w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    ∫ y, scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PY w) α) y ∂PY ≤ ∫ y, scoreΓ w h α A y ∂PY := by sorry

end MultivarScores.LevelSet
