-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_delta_pp_eq
-- name    : MultivarScores.LevelSet.delta_pp_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:54.982124+00:00
-- url     : https://prove2.me/theorems/3190c21d-12d9-4d01-8fb6-2b41fd3d608f
-- title:
--   Proof of Theorem 2, p. 33 — Δ″: (S′)^Γ(A, y) − (S′)^Γ(L, y) = ∫ (α − w(z − y))(𝟙_{A∖L} − 𝟙_{L∖A}) h dz
-- statement:
--   Let $w,h:\mathbb R^d\to\mathbb R$ be measurable with $w\ge0$, $h\ge0$ and $h$ integrable, let $\alpha>0$, and let $A,L\subseteq\mathbb R^d$ be Borel sets. Fix a realization $y\in\mathbb R^d$ such that $z\mapsto w(z-y)h(z)$ is integrable. Then the difference of level set scores is
--
--   $$(S')^\Gamma(A,y;w,h,\alpha)-(S')^\Gamma(L,y;w,h,\alpha)=\int_{\mathbb R^d}\bigl(\alpha-w(z-y)\bigr)\bigl[\mathbb 1_{A\setminus L}(z)-\mathbb 1_{L\setminus A}(z)\bigr]h(z)\,dz.$$
--
--   This is the quantity $\Delta''$ of the proof of Theorem 2, with $\Sigma_{+-}=A\setminus L$ and $\Sigma_{-+}=L\setminus A$. Taking the expectation over $y$ turns it into display (19).
--
--   **Formalization Note** The paper's partition uses $\{\Xi[Y]>\alpha\}$ while its target is $L=\{f_Y*w\ge\alpha\}$; the statement is given for an arbitrary Borel $L$, which covers the target $L=L(f_Y*w;\alpha)$. The integrability of $w(\cdot-y)h$ is Assumption 1(c) for this $y$; without it the Bochner integrals would be $0$. $w\ge0$ and $\alpha>0$ are kept from Theorem 2's hypotheses.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 33, proof of Theorem 2, display of Δ″ (B₁, B₂, Σ±±)

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem delta_pp_eq {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ)
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (α : ℝ) (hα : 0 < α) (A L : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) (hL : MeasurableSet L)
    (y : MultivarScores.L2Rule.E d) (hwy_int : Integrable (fun z => w (z - y) * h z)) :
    scoreΓ w h α A y - scoreΓ w h α L y =
      ∫ z, (α - w (z - y)) * ((A \ L).indicator 1 z - (L \ A).indicator 1 z) * h z := by sorry

end MultivarScores.LevelSet
