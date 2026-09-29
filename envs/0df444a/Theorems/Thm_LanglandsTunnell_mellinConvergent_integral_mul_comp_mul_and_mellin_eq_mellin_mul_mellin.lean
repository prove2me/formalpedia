-- Prove2me | Theorems.Thm_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
-- name    : LanglandsTunnell.mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e2ed40a3-a382-5c4c-aea8-47ccde557bfe
-- title:
--   Mellin transform of a multiplicative convolution
-- statement:
--   Let $\varphi, g : \mathbb{R} \to \mathbb{C}$ and $z \in \mathbb{C}$. Assume that $\varphi$ and $g$ are almost everywhere strongly measurable for Lebesgue measure restricted to $(0,\infty)$, that $\varphi$ has convergent Mellin transform at $1-z$, i.e. $t \mapsto (t:\mathbb{C})^{-z} \varphi(t)$ is integrable on $(0,\infty)$, and that $g$ has convergent Mellin transform at $z$, i.e. $u \mapsto (u:\mathbb{C})^{z-1} g(u)$ is integrable on $(0,\infty)$. Then the function $T(r) = \int_{(0,\infty)} \varphi(t)\, g(rt)\, dt$ (the Bochner integral, which is defined with value $0$ wherever the integrand fails to be integrable) itself has convergent Mellin transform at $z$, that is $r \mapsto (r:\mathbb{C})^{z-1} T(r)$ is integrable on $(0,\infty)$, and its Mellin transform factorises: $$\operatorname{mellin} T(z) = \operatorname{mellin}\varphi(1-z)\cdot \operatorname{mellin} g(z).$$ Here $\operatorname{mellin} f(s) = \int_{(0,\infty)} (t:\mathbb{C})^{s-1} f(t)\, dt$ in the sense of Mathlib's `mellin`, and `MellinConvergent f s` is integrability of that integrand on $(0,\infty)$.
--
--   This is the multiplicative convolution theorem for the Mellin transform, in the absolutely convergent range dictated by the two hypotheses on the strips of convergence. It serves as an analytic tool in the archimedean part of the converse theorem, where it is used to produce values of $z$ at which a Mellin transform of a Gaussian times a torus-kernel integral is non-zero, in [`LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero`](thm.html#LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero) and its two-sheet analogue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin.lean

import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
    (φ g : ℝ → ℂ) (z : ℂ)
    (hφm : AEStronglyMeasurable φ (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hgm : AEStronglyMeasurable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hφ : MellinConvergent φ (1 - z)) (hg : MellinConvergent g z) :
    MellinConvergent (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z ∧
      mellin (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z = mellin φ (1 - z) * mellin g z := by sorry
