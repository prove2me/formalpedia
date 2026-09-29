-- Prove2me | Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
-- name    : LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0c148327-f412-5ca2-806d-77ccd1f57d27
-- title:
--   Gaussian torus transform: Mellin transform in J-form
-- statement:
--   Let $a$ be a non-zero real number, let $p,q,\kappa,C$ be complex numbers, and let $H:\mathbb R\to\mathbb C$ be the function
--   $$H(\sigma')=e^{-\pi a^{2}\sigma'^{2}}\int_{0}^{\infty}\Bigl(C\,\tfrac{|a|\sigma'}{w}\cdot 4\!\int_{0}^{\infty} r^{p}e^{-\pi r^{2}}\Bigl(\tfrac{|a|\sigma'/w}{r}\Bigr)^{q}e^{-\pi((|a|\sigma'/w)/r)^{2}}\,\frac{dr}{r}\Bigr)\,w^{\kappa}e^{-\pi(w^{-2}+a^{2}w^{2})}\,dw,$$
--   all powers being principal complex powers of the indicated real quantities. Let $z$ be a complex number with $\operatorname{Re}(z+q)>-1$ and $\operatorname{Re}(z+p)>-1$. Then three things hold simultaneously: first, $H$ is Mellin convergent at $z$, i.e. $\sigma\mapsto \sigma^{z-1}H(\sigma)$ is integrable on $(0,\infty)$; second, the function
--   $$(w,r)\mapsto\bigl(1+(wr)^{-2}\bigr)^{-\frac{z+q+1}{2}}w^{\kappa-1-q}r^{p-q-1}e^{-\pi(r^{2}+w^{-2}+a^{2}w^{2})}$$
--   is integrable for the product of Lebesgue measure restricted to $(0,\infty)$ with itself; and third,
--   $$\mathcal M H(z)=2C\,|a|^{1+q}(\pi a^{2})^{-\frac{z+q+1}{2}}\,\Gamma\!\Bigl(\frac{z+q+1}{2}\Bigr)\int_{0}^{\infty}\!\!\int_{0}^{\infty}\bigl(1+(wr)^{-2}\bigr)^{-\frac{z+q+1}{2}}w^{\kappa-1-q}r^{p-q-1}e^{-\pi(r^{2}+w^{-2}+a^{2}w^{2})}\,dr\,dw,$$
--   with $\Gamma$ the complex Gamma function.
--
--   This is the closed evaluation of the Mellin transform of the Gaussian torus transform in which the $\sigma'$-integration is carried out first by Euler's integral, so that all dependence on $z$ is concentrated in the explicit factor $(\pi a^{2})^{-(z+q+1)/2}\Gamma((z+q+1)/2)$ together with the double integral $J(z)$. It is used by [`LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep`](thm.html#LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep) and by [`LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le`](thm.html#LanglandsTunnell.norm_mellin_gaussTorusTransform_halfStep_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent H z ∧
    Integrable (fun v : ℝ × ℝ =>
        (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
          (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) ∧
    mellin H z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
          (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) := by sorry
