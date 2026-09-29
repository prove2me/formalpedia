-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
-- name    : LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/9b4f92fb-c1bf-5c02-833c-48a760dc9455
-- title:
--   Archimedean triple integral as tfrac12Γ_ℝ times a Mellin transform
-- statement:
--   Let $b>0$ be real, let $p\in\mathbb C$, and let $g:\mathbb R\to\mathbb C$ be measurable and subject to the bound $\|g(t)\|\le C\,(1+t^{-\sigma})$ for all $t>0$, where $C,\sigma$ are real with $\sigma\ge 0$. Let $K:\mathbb R\to\mathbb C$ be measurable and subject to the bound $\|K(w)\|\le C_K\,(w^{N}+w^{-N})\,e^{-\pi(w^{-2}+b\,w^{2})}$ for all $w>0$, with $C_K,N$ real (no sign condition is imposed on $C$ or $C_K$). Let $H:\mathbb R\to\mathbb C$ be the function $H(\sigma')=e^{-\pi b\sigma'^{2}}\int_{w\in(0,\infty)}g(\sigma'/w)K(w)\,dw$. The assertion is that there exists a real $\sigma_0$ such that for every $s\in\mathbb C$ with $\operatorname{Re}s>\sigma_0$ the following three things hold: first, the function $(y,y_1,y_2)\mapsto y^{\,s-2}\bigl(y_1^{\,p}K(y_2)\,e^{-\pi(y_1^{-2}+b\,y^{2}y_1^{2})}\,g(yy_1/y_2)\bigr)$ is integrable for the triple product of Lebesgue measure restricted to $(0,\infty)$; second, `MellinConvergent H (s-1)` holds, i.e. the Mellin integrand $t\mapsto t^{\,s-2}H(t)$ is integrable on $(0,\infty)$; and third, the iterated integral $\int_0^\infty y^{\,s-2}\int_0^\infty\int_0^\infty y_1^{\,p}K(y_2)\,e^{-\pi(y_1^{-2}+b\,y^{2}y_1^{2})}\,g(yy_1/y_2)\,dy_2\,dy_1\,dy$ equals $\tfrac12\,\Gamma_{\mathbb R}(s-p-2)\cdot\mathcal MH(s-1)$, with $\Gamma_{\mathbb R}(z)=\pi^{-z/2}\Gamma(z/2)$.
--
--   This is the analytic core of the archimedean zeta-integral computations over the positive octant: it separates off the $y_1$-variable as a $\Gamma_{\mathbb R}$-factor and identifies the remaining integral as the Mellin transform of the kernel transform $H$, on a right half-plane whose abscissa is produced by the statement rather than specified. It is used by the archimedean $GL_3\times GL_1$ zeta-integral lemmas of the cubic-induction step, for the various harmonic and Gaussian test functions occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
    (b : ℝ) (hb : 0 < b) (p : ℂ)
    (g : ℝ → ℂ) (hgm : Measurable g) (C σ : ℝ) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (K : ℝ → ℂ) (hKm : Measurable K) (CK N : ℝ)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * b * σ' ^ 2)) : ℂ) * ∫ w in Ioi (0 : ℝ), g (σ' / w) * K w) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) * (((q.2.1 : ℝ) : ℂ) ^ p * K q.2.2 *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + b * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) * g (q.1 * q.2.1 / q.2.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s - 1) ∧
      ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ p * K y₂ * (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + b * y ^ 2 * y₁ ^ 2))) : ℂ) * g (y * y₁ / y₂) =
        (1 / 2 : ℂ) * Complex.Gammaℝ (s - p - 2) * mellin H (s - 1) := by sorry
