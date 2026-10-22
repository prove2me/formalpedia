-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_cdf_level_set_consistent
-- name    : MultivarScores.LevelSet.cdf_level_set_consistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:49.944022+00:00
-- url     : https://prove2.me/theorems/d104e626-8fb3-4cfd-8e7e-848665185ee2
-- title:
--   (13), §4.2.2, p. 16 — the CDF level set score (MCRPS′)^Γ is consistent for L(F_Y; α)
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R$ be measurable, nonnegative and integrable, let $P_Y$ be any probability measure on $\mathbb R^d$ with multivariate CDF $F_Y(z)=P_Y\{s: s\le z\}$, let $\alpha>0$, and let $A\subseteq\mathbb R^d$ be a Borel set. With the CDF level set score
--
--   $$(\mathrm{MCRPS}')^\Gamma(A,y;h,\alpha)=\int_{\mathbb R^d}\bigl(\alpha-\mathbb 1\{z\ge y\}\bigr)\,\mathbb 1\{z\in A\}\,h(z)\,dz \qquad(13)$$
--
--   and the $\alpha$ CDF level set $L(F_Y;\alpha)=\{z: F_Y(z)\ge\alpha\}$,
--
--   $$\mathbb E_{P_Y}\bigl[(\mathrm{MCRPS}')^\Gamma(L(F_Y;\alpha),\bullet;h,\alpha)\bigr]\le\mathbb E_{P_Y}\bigl[(\mathrm{MCRPS}')^\Gamma(A,\bullet;h,\alpha)\bigr].$$
--
--   That is, (13) is a consistent scoring function for the $\alpha$ CDF level set, the instance $w=u=\mathbb 1\{\cdot\ge0\}$ of Theorem 2, for which $f_Y*u=F_Y$.
--
--   **Formalization Note** The score is the Setting's `scoreΓ heaviside h α`, and $u(z-y)=\mathbb 1\{z\ge y\}$ in the componentwise order. No further integrability hypothesis is needed because $0\le u\le1$ and $h$ is integrable. The level set is stated with the CDF $F_Y$ itself, as on p. 16.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 16, §4.2.2, display (13)

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem cdf_level_set_consistent {d : ℕ} (h : MultivarScores.L2Rule.E d → ℝ)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    ∫ y, scoreΓ MultivarScores.L2Rule.heaviside h α (levelSet (MultivarScores.L2Rule.cdf PY) α) y ∂PY ≤ ∫ y, scoreΓ MultivarScores.L2Rule.heaviside h α A y ∂PY := by sorry

end MultivarScores.LevelSet
