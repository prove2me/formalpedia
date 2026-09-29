-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand
-- name    : LanglandsTunnell.Converse.integrable_dualThetaFree_integrand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/2903d6f6-2f3c-5434-9516-c652c59babf4
-- title:
--   Integrability of the θ-free dual Iwasawa integrand
-- statement:
--   Fix a real archimedean parameter $P_2$ (a `RealArchParam`, either a principal pair $(u_1,a_1,u_2,a_2)$ or a discrete datum $(u,k)$ with $k\ge 1$) and a datum $D :$ `ArchDatumR` $P_2$, that is a function $W$ on $2\times2$ real matrices, smooth on the invertible locus, with $W(\mathrm{unip}(x)g)=\psi(x)W(g)$, $W(z\cdot g)=\chi_{P_2}(z)|z|W(g)$ for $z\ne 0$, together with entire zeta functions satisfying the stated integrability, functional equation, finite-order and moderate-decay conditions at $|y|\ge 1$ and $0<|y|\le 1$. Let $a\in\mathbb R$, $a\ne 0$, let $\beta,\gamma\in\mathbb C$, $m,n\in\mathbb N$, let $S:\mathbb R\to\mathbb C$ be measurable with $\|S(y)\|\le C_S$ for all $y$, and let $a_1\ne 0$, $a_2>0$ be real. The assertion is that the function
--   $$(x,y_1,y_2)\mapsto (y_1^{-1})^{n}\,S(y_1)\,|y_1|^{\beta}\,y_2^{\gamma}\,e^{-\pi x^2/(a_2y_1)^2}\,\psi(ax)\,\bigl(a_1y_2-(a_2y_2)^{-1}+i\,x/(a_2y_1)\bigr)^{m}\,e^{-\pi\left((a_2y_2)^{-2}+y_1^{-2}+a_1^2y_2^2\right)}\;W\!\left(\begin{smallmatrix}a\,y_1/y_2&0\\0&1\end{smallmatrix}\right)$$
--   with $\psi(t)=e^{2\pi i t}$, the powers $\beta,\gamma$ being complex powers of the nonnegative reals $|y_1|$ and $y_2$, is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for Lebesgue measure in $x$ and $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the integrability input for the archimedean Rankin–Selberg computation in the converse-theorem part of the Langlands–Tunnell argument: it licenses Fubini and the passage to an Iwasawa-coordinate integral for the $\theta$-free form of the dual integrand, with no restriction on the exponents $\beta,\gamma$. It is used in the evaluation of the dual torus pair for discrete-series data with a harmonic Gaussian shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.integrable_dualThetaFree_integrand
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0)
    (β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hSm : Measurable S) (CS : ℝ) (hSb : ∀ y : ℝ, ‖S y‖ ≤ CS)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * (q.1 ^ 2 / (a₂ * q.2.1) ^ 2))) : ℂ) * ArchR.psi (a * q.1) *
          ((((a₁ * q.2.2 - (a₂ * q.2.2)⁻¹ : ℝ) : ℂ)) + Complex.I * (((q.1 / (a₂ * q.2.1) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * q.2.2) ^ 2)⁻¹ + (q.2.1 ^ 2)⁻¹ + a₁ ^ 2 * q.2.2 ^ 2))) : ℂ) *
          D.W (ArchR.diagOne (a * (q.2.1 / q.2.2))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))))) := by sorry
