-- Prove2me | Theorems.Thm_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
-- name    : MellinParseval.integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6ec536da-8a75-5612-a160-6ac7fedfe2fb
-- title:
--   Integrability of the Mellin profile of a strip-holomorphic family
-- statement:
--   Let $\sigma,\sigma_0$ be real numbers with $0<\sigma_0$, let $f:\mathbb{C}\to\mathbb{C}$, and let $m:\mathbb{R}\to\mathbb{R}$. Assume that $f$ is complex differentiable on the open vertical strip $\{s\in\mathbb{C} : |\operatorname{Re}(s)-\sigma|<\sigma_0\}$, that $m$ is integrable on $\mathbb{R}$ for Lebesgue measure, and that $m$ majorises $f$ on every line of the strip: for all real $\sigma'$ with $|\sigma'-\sigma|<\sigma_0$ and all real $t$, $\|f(\sigma'+it)\|\le m(t)$. The conclusion is that the function
--   $$y\mapsto \frac{y^{-\sigma}}{y}\int_{\mathbb{R}} y^{\sigma+it}\,f(\sigma+it)\,dt$$
--   is integrable on the open half-line $(0,\infty)$, where $y^{-\sigma}/y$ is the real power, coerced into $\mathbb{C}$, and $y^{\sigma+it}$ is the complex power of the coercion of $y$. Thus the Mellin profile $P(y)=\int_{\mathbb{R}} y^{\sigma+it}f(\sigma+it)\,dt$ of $f$ along the central line satisfies $\int_0^\infty y^{-\sigma}\|P(y)\|\,dy/y<\infty$, integrability being asserted in the Bochner sense for Lebesgue measure restricted to $(0,\infty)$.
--
--   This supplies the profile-integrability hypothesis needed to apply the Mellin–Parseval identity to a family holomorphic on a vertical strip with an integrable majorant on the lines of that strip; the gain comes from shifting the contour to $\operatorname{Re}(s)=\sigma\pm\sigma_0/2$, which bounds $y^{-\sigma}\|P(y)\|$ by a constant times $y^{\pm\sigma_0/2}$. It is used in the computation of the inner product of a pseudo-Eisenstein series against an automorphic form, where the line integral of a section is paired with a character of the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MellinParseval.integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
    (σ σ₀ : ℝ) (_hσ₀ : 0 < σ₀) (f : ℂ → ℂ) (m : ℝ → ℝ)
    (_hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (_hm : Integrable m)
    (_hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t) :
    IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * f ((σ : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi 0) := by sorry
