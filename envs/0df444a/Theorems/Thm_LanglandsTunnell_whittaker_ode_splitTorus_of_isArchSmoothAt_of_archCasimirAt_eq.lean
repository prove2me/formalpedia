-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
-- name    : LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8772f9b5-45fa-56ff-a655-c0f66686a98f
-- title:
--   Whittaker's ODE on the split torus at a real place
-- statement:
--   Let $K$ be a number field, $w$ a real infinite place of $K$, $W\colon GL_2(\mathbb{A}_K)\to\mathbb{C}$ a function on the adelic group `AdelicGL2 (𝓞 K) K`, $k_0\in\mathbb{Z}$ and $\nu\in\mathbb{C}$. Assume: (i) `IsArchSmoothAt hw W`, i.e. for every $g$ the map sending a $2\times 2$ real matrix $e$ to $W(g\cdot \mathrm{incl}_w(e))$ is $C^\infty$ on the set $\{\det e\neq 0\}$, where $\mathrm{incl}_w$ places an invertible real matrix at $w$; (ii) the Casimir eigen-equation at $w$, $-\big(\tfrac14 H^2W-\tfrac12 HW+E(F^-W)\big)=(\tfrac14-\nu^2)\,W$, the operators being the right derivatives `archDerivAt` along the one-parameter flows at $w$ in the directions `ArchDir.H`, `.E`, `.Fm`; (iii) the predicate `HasArchCharacterAt₀ K w (archWeightCharAt hw k₀) W`, expressing that $W$ transforms under right translation by the subgroup `rowIsometrySubgroup₀` of $GL_2(K_w)$ through the $k_0$-th power of the character `archWeightOneAt hw`; (iv) $W\big(n_w(x)\,g\big)=e^{2\pi i x}W(g)$ for all $x\in\mathbb{R}$ and all $g$, with $n_w(x)=\mathrm{incl}_w\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Let $g$ have trivial archimedean component, $\mathrm{glArch}(g)=1$. Put $a(y)=\mathrm{incl}_w\,\mathrm{diag}(e^{\log y/2},e^{-\log y/2})$. Then $f_+(y)=W(a(y)g)$ is differentiable on $(0,\infty)$ with differentiable derivative there, and $y^2f_+''(y)+\big(\tfrac14-\nu^2+2\pi k_0 y-4\pi^2y^2\big)f_+(y)=0$ for all $y>0$; and the same three assertions hold for $f_-(y)=W\big(\mathrm{incl}_w(J\,\mathrm{diag}(e^{\log y/2},e^{-\log y/2}))\,g\big)$, with $J=\mathrm{diag}(-1,1)$ (Mathlib's `UpperHalfPlane.J`), with $-k_0$ in place of $k_0$.
--
--   This is Whittaker's classical second-order differential equation for the radial part of a Whittaker function on $GL_2(\mathbb{R})$ in Iwasawa coordinates, in the adelic setting at a real place and recorded on both connected components of the split torus. It is used in the analysis of Whittaker coefficients of cuspidal forms (regularity, the torus ODE, growth and separation of solutions) and in assembling the archimedean data and the Whittaker factorisation used on the Langlands–Tunnell side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
open NumberField AutomorphicForm

theorem LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (W : AdelicGL2 (𝓞 K) K → ℂ)
    (k₀ : ℤ) (ν : ℂ)
    (hsm : IsArchSmoothAt hw W)
    (hΩ : archCasimirAt hw W = (1 / 4 - ν ^ 2) • W)
    (hk : HasArchCharacterAt₀ K w (archWeightCharAt hw k₀) W)
    (hψ : ∀ (x : ℝ) (g : AdelicGL2 (𝓞 K) K),
      W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g)
    (g : AdelicGL2 (𝓞 K) K) (hg : AdelicLevel.glArch (𝓞 K) K g = 1) :
    (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
    (DifferentiableOn ℝ
        (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ
        (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv
              (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0) := by sorry
