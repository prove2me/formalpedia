-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/37f883a5-7310-5762-b159-b7a802ebdf59
-- title:
--   Integrability of the x-affine Gaussian against a torus pair
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, a class $b\in\mathbb Z/2$, and a function $W:\mathbb R\to\mathbb C$ which is continuous on $\{t\in\mathbb R: t\neq 0\}$ and satisfies two conditions: for every $t>0$, $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{r>0} r^{\nu_1}e^{-\pi r^2}\,(t/r)^{\nu_2}e^{-\pi (t/r)^2}\,\frac{dr}{r}$ (the exponent being the natural-number representative of $b$), and the parity law $W(-t)=(-1)^{b}W(t)$ for all real $t$ (so on $t>0$ the first condition reads $2W(t)=t\,G_{\nu_1,\nu_2}(t)$). Fix also a real archimedean parameter $P_2$ — either a principal datum $(u_1,a_1,u_2,a_2)$ or a discrete datum $(u,k)$ with $k\ge 1$ — and an archimedean Whittaker datum $D$ for $P_2$, whose Whittaker function $D.W$ on $2\times 2$ real matrices is smooth on the relevant set, transforms by $\psi(x)=e^{2\pi i x}$ under unipotents and by the central character, and has the stated zeta-integral, functional-equation, finite-order and decay properties. Fix $a\in\mathbb R$ with $a\neq 0$ and $c_0,c_1\in\mathbb C$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$, every $y_1\neq 0$ and every $y_2>0$, the function $$(x,t)\mapsto e^{-\pi x^2/y_1^2}(c_0+c_1ix)\,e^{2\pi i a t x}\cdot W(t)\,D.W\!\left(\begin{smallmatrix}aty_1/y_2&0\\0&1\end{smallmatrix}\right)|t|^{s-1/2}\,t^{-2}$$ is integrable on $\mathbb R^2$ for the product of Lebesgue measures.
--
--   This is the absolute-convergence statement that licenses the Fubini interchange taking the Gaussian moment in the affine variable $x$ inside the torus variable $t$ in the Iwasawa unfolding of a Rankin–Selberg integral, for a Whittaker profile with a single Gaussian-convolution sheet and a parity law. It is used by the even principal-series torus-pair identities [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile) and its weight-one and discrete-profile companions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (c₀ c₁ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry
