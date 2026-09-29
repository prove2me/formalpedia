-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_profiles
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_profiles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/8f5b2722-b59b-5a35-a7a5-39292b1f6d2c
-- title:
--   Integrability of the unfolded (x,t)-integrand for Gaussian-convolution profiles
-- statement:
--   Fix complex parameters $\nu_1,\nu_2,\mu_1,\mu_2$, classes $a_1,a_2,c \in \mathbb{Z}/2$, and a function $W : \mathbb{R} \to \mathbb{C}$ continuous on $\{t \neq 0\}$ whose two parity combinations are weight-one Gaussian-convolution profiles: for every $b \in \mathbb{Z}/2$ and every $t > 0$, $W(t) + (-1)^{b} W(-t) = t \cdot 4\int_0^\infty r^{\nu_1 + \mathrm{sh}(a_1+b)} e^{-\pi r^2} (t/r)^{\nu_2 + \mathrm{sh}(a_2+b)} e^{-\pi (t/r)^2}\,\frac{dr}{r}$, where $\mathrm{sh}(a) = 0$ for $a = 0$ and $1$ otherwise. Fix a real archimedean parameter $P_2$ (principal or discrete) and a real archimedean Whittaker datum $D$ for $P_2$, i.e. a function $D.W$ on $2\times 2$ real matrices that is smooth on the invertible locus, transforms by $\psi$ under left unipotent translation and by the central character under scalars, and whose zeta integrals converge in a right half-plane, continue to entire functions of finite order satisfying the expected functional equation, with the prescribed decay at $|y| \ge 1$ and near $y = 0$. Assume, with $\rho \in \mathbb{C}$, that $D.W(\mathrm{diag}(\tau,1)) = \rho\,\tau \cdot 4\int_0^\infty r^{\mu_1} e^{-\pi r^2}(\tau/r)^{\mu_2} e^{-\pi(\tau/r)^2}\,\frac{dr}{r}$ for $\tau > 0$, and that $D.W(\mathrm{diag}(-\tau,1)) = (-1)^{c} D.W(\mathrm{diag}(\tau,1))$ for $\tau > 0$. Let $a \neq 0$ be real and $c_0,c_1 \in \mathbb{C}$. Then there is $\sigma \in \mathbb{R}$ such that for every $s$ with $\operatorname{Re} s > \sigma$, every $y_1 \neq 0$ and every $y_2 > 0$, the function $$(x,t) \mapsto e^{-\pi x^2/y_1^2}\,(c_0 + c_1 i x)\,\psi(a t x)\cdot W(t)\,D.W\bigl(\mathrm{diag}(a t y_1/y_2, 1)\bigr)\,|t|^{s - 1/2}\,t^{-2}$$ is integrable on $\mathbb{R} \times \mathbb{R}$ for the product of Lebesgue measures, where $\psi(x) = e^{2\pi i x}$. The threshold $\sigma$ is uniform in $s$, $y_1$ and $y_2$.
--
--   This is the absolute-convergence input for the Iwasawa unfolding of an archimedean Rankin–Selberg integral in the converse-theorem step of the Langlands–Tunnell argument: it supplies the Fubini hypothesis needed to interchange the $x$- and $t$-integrations. It is used in the evaluation of the unfolded torus pair for weight-one Gaussian profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_profiles.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_mulConvGaussian_profiles
    (ν₁ ν₂ μ₁ μ₂ : ℂ) (a₁ a₂ c : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (ρ : ℂ)
    (hD : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha : a ≠ 0) (c₀ c₁ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry
