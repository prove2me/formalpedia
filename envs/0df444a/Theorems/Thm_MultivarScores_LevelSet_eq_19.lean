-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_eq_19
-- name    : MultivarScores.LevelSet.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:58.696182+00:00
-- url     : https://prove2.me/theorems/7cf0ea37-a9dd-4558-87fb-9c1b39e703ff
-- title:
--   (19), proof of Theorem 2, p. 34 — 𝔼(S′)^Γ(A,•) − 𝔼(S′)^Γ(L,•) = ∫ (α − f_Y ∗ w)(𝟙_{A∖L} − 𝟙_{L∖A}) h dz
-- statement:
--   Let $P_Y$ be a probability measure on $\mathbb R^d$ (the distribution of the observation $Y$). Let $w,h:\mathbb R^d\to\mathbb R$ be measurable with $w\ge0$, $h\ge0$, $h$ integrable, and $(s,z)\mapsto w(z-s)h(z)$ integrable with respect to $P_Y\otimes\mathcal L^d$. Let $\alpha>0$, let $A\subseteq\mathbb R^d$ be Borel, and write $L=L(f_Y*w;\alpha)=\{z: (f_Y*w)(z)\ge\alpha\}$. Then
--
--   $$\mathbb E_{P_Y}\bigl[(S')^\Gamma(A,\bullet;w,h,\alpha)\bigr]-\mathbb E_{P_Y}\bigl[(S')^\Gamma(L,\bullet;w,h,\alpha)\bigr]=\int_{\mathbb R^d}\bigl(\alpha-(f_Y*w)(z)\bigr)\bigl[\mathbb 1_{A\setminus L}(z)-\mathbb 1_{L\setminus A}(z)\bigr]h(z)\,dz.$$
--
--   This is display (19), $\Delta'=\mathbb E_{P_Y}[\Delta'']$. Since the integrand is nonnegative ($\alpha-f_Y*w>0$ on $A\setminus L$ and $\le0$ on $L\setminus A$), it yields the consistency of $(S')^\Gamma$.
--
--   **Formalization Note** The paper's sets $\Sigma_{+-},\Sigma_{-+}$ are built from $\{\Xi[Y]>\alpha\}$ (a printed slip); here $\Sigma_{+-}=A\setminus L$ and $\Sigma_{-+}=L\setminus A$ with $L=\{f_Y*w\ge\alpha\}$ as in (9), which changes nothing because the integrand vanishes on $\{f_Y*w=\alpha\}$. The product-integrability hypothesis pins down Assumption 1 and Theorem 2's "$(S')^\Gamma(A,\bullet)f_Y(\bullet)$ is integrable": with $w,h\ge0$ it makes $y\mapsto (S')^\Gamma(B,y)$ $P_Y$-integrable for every Borel $B$ at once, including $L$. The paper allows $w$ to be a local Borel measure (Assumption 1(a)); here $w$ is a measurable function, a disclosed specialization that excludes only the Dirac kernel $w=\delta_0$ (the density level set score (12)).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 34, proof of Theorem 2, display (19)

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem eq_19 {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d => w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    (∫ y, scoreΓ w h α A y ∂PY) - ∫ y, scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PY w) α) y ∂PY =
      ∫ z, (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z := by sorry

end MultivarScores.LevelSet
