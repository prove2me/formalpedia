-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xQuadraticGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_xQuadraticGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ccdf10f3-5c3b-5f4a-b5c6-372aa4f1940f
-- title:
--   Joint integrability of a quadratic Gaussian against the torus pair
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb{C}$, a class $b\in\mathbb{Z}/2$, and a function $W:\mathbb{R}\to\mathbb{C}$ that is continuous on $\{t\in\mathbb{R}: t\neq 0\}$ and satisfies two conditions: for every $t>0$,
--   $$W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{r>0}\bigl(r^{\nu_1}e^{-\pi r^2}\bigr)\bigl((t/r)^{\nu_2}e^{-\pi (t/r)^2}\bigr)\,\frac{dr}{r},$$
--   where the exponent $(-1)^b$ uses the representative $b.\mathrm{val}$, and the parity law $W(-t)=(-1)^{b}W(t)$ for all real $t$. Fix furthermore a real archimedean parameter $P_2$ (principal or discrete series type) and an archimedean Whittaker datum $D$ for $P_2$, i.e. a function $D.W$ on real $2\times 2$ matrices, smooth on the invertible locus, with the unipotent law $D.W(n(x)g)=\psi(x)D.W(g)$ and central law, together with the package of zeta integrals, their entire completions, functional equation, finite order and the decay estimates at $|y|\ge 1$ and $0<|y|\le 1$. Fix also $a\in\mathbb{R}$ with $a\neq 0$ and constants $c_0,c_1,c_2\in\mathbb{C}$. The assertion is that there is a real abscissa $\sigma$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re} s>\sigma$, every $y_1\neq 0$ and every $y_2>0$, the function
--   $$(x,t)\mapsto e^{-\pi x^2/y_1^2}\bigl(c_0+c_1 i x+c_2 x^2\bigr)\,\psi(atx)\cdot W(t)\,D.W\!\left(\begin{smallmatrix} aty_1/y_2 & 0\\ 0&1\end{smallmatrix}\right)|t|^{\,s-1/2}\,t^{-2}$$
--   is integrable on $\mathbb{R}\times\mathbb{R}$ for the product of Lebesgue measures, where $\psi(x)=e^{2\pi i x}$.
--
--   This is the Fubini licence for the quadratic step in the $x$-variable of the converse-theorem computation: it certifies that the two-dimensional integral of a Gaussian with a quadratic polynomial factor, twisted by the additive character $\psi(atx)$ and paired with the torus data $W(t)$ and $D.W$ of the archimedean Whittaker datum, converges absolutely in a right half-plane. It is used in the identification of the theta-free Iwasawa integral with the corresponding post-Gaussian torus integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_xQuadraticGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_xQuadraticGaussian_psi_mul_torusPair_of_mulConvGaussian_sheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (c₀ c₁ c₂ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ) + c₂ * (q.1 : ℂ) ^ 2) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry
