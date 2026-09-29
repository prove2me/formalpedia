-- Prove2me | Theorems.Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
-- name    : MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/43389181-ae7e-5ac2-9d91-70ffd08f20ad
-- title:
--   Paley–Wiener for the Mellin transform on the line
-- statement:
--   Let $h\colon\mathbb R\to\mathbb C$ be a function that is $C^\infty$ (smoothness of order $\top$, i.e. infinitely differentiable on $\mathbb R$) and has compact support, and consider the function
--   $$M(s)=\int_{\mathbb R} h(u)\,e^{su}\,du\qquad(s\in\mathbb C),$$
--   the Bochner integral against Lebesgue measure on $\mathbb R$. The conclusion is a conjunction of three assertions. First, $s\mapsto M(s)$ is complex differentiable at every point of $\mathbb C$, i.e. entire. Second, for every natural number $n$ and every real $\sigma_0$ there exists a real constant $C\ge 0$ such that for all real $\sigma'$ with $|\sigma'|\le\sigma_0$ and all real $t$ one has $(1+|t|)^n\,\lVert M(\sigma'+it)\rVert\le C$; thus $M$ decays faster than any polynomial along vertical lines, uniformly on each closed vertical strip. Third, for all real $\sigma'$ and $u$,
--   $$h(u)=\frac{1}{2\pi}\int_{\mathbb R} M(\sigma'+it)\,e^{-(\sigma'+it)u}\,dt,$$
--   the inversion formula on an arbitrary vertical line, again as a Bochner integral in $t$.
--
--   This is the Paley–Wiener description of the Mellin transform of a smooth compactly supported function of the logarithmic variable, $M(s)=\int_0^\infty h(\log y)\,y^{s}\,dy/y$: entire, rapidly decreasing on vertical strips, and recovered by contour inversion on any vertical line. It supplies the analytic input for the constructions of Paley–Wiener test profiles for automorphic forms, where an entire family of induced sections is multiplied by $M(s)$ and integrated along a vertical line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
    (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))) ∧
    (∀ (n : ℕ) (σ₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖∫ u : ℝ, h u * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))‖ ≤ C) ∧
    (∀ (σ' u : ℝ), h u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) := by sorry
