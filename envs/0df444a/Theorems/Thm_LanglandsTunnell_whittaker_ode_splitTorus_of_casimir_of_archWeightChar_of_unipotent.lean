-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
-- name    : LanglandsTunnell.whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0d6ab3ac-70e7-53cb-8b06-1bde2b736831
-- title:
--   Whittaker's equation on the split torus from the Casimir eigen-equation
-- statement:
--   Let $F : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$, let $k_0$ be an integer and $\nu$ a complex number. Assume: (i) the function on $2\times 2$ real matrix entries $e$ given by $F$ of the invertible matrix determined by $e$ when $\det e \neq 0$ (and by $F(1)$ otherwise) is twice continuously differentiable on the open set $\{e \mid \det e \neq 0\}$; (ii) $F(n(x)m) = e^{2\pi i x} F(m)$ for all real $x$ and all $m$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; (iii) $F(mk) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(k)\,F(m)$ for every $k$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb{R})$; (iv) at every $m$, with $a(t) = \mathrm{diag}(e^{t},e^{-t})$ and $n^{-}(s) = \begin{pmatrix}1&0\\s&1\end{pmatrix}$, $$-\Big(\tfrac14 \partial_t\partial_s F(m a(t) a(s))\big|_0 - \tfrac12 \partial_t F(m a(t))\big|_0 + \partial_t\partial_s F(m n(t) n^{-}(s))\big|_0\Big) = \big(\tfrac14 - \nu^2\big) F(m).$$ Then, writing $f_+(y) = F(a(\tfrac12\log y))$ and $f_-(y) = F(\mathrm{UpperHalfPlane.J}\cdot a(\tfrac12\log y))$, each of $f_\pm$ is differentiable on $(0,\infty)$ with differentiable derivative there, and for all $y > 0$ one has $y^2 f_\pm''(y) + \big(\tfrac14 - \nu^2 \pm 2\pi k_0 y - 4\pi^2 y^2\big) f_\pm(y) = 0$, the sign $+$ for $f_+$ and $-$ for $f_-$.
--
--   This is the classical derivation of Whittaker's differential equation for a $\mathrm{GL}_2(\mathbb{R})$ Whittaker function of weight $k_0$ and Casimir eigenvalue $\tfrac14 - \nu^2$, restricted to the split torus in Iwasawa coordinates on each of the two connected components. It feeds the archimedean analysis of the converse theorem, being used by [`LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen`](thm.html#LanglandsTunnell.Converse.ArchDatumR.negSheet_ode_and_growth_and_mellin_eq_of_archWeightChar_of_isCasimirEigen); no central or growth condition is imposed and $\nu$ is arbitrary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
open AutomorphicForm

theorem LanglandsTunnell.whittaker_ode_splitTorus_of_casimir_of_archWeightChar_of_unipotent
    (F : GL (Fin 2) ℝ → ℂ) (k₀ : ℤ) (ν : ℂ)
    (hF : ContDiffOn ℝ 2
      (fun e : Fin 2 → Fin 2 → ℝ =>
        F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h
          else 1))
      {e | (Matrix.of e).det ≠ 0})
    (hψ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
      F (unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * F m)
    (hk : ∀ (k : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ),
      F (m * k) = (archWeightCharℝ k₀ k : ℂ) * F m)
    (hΩ : ∀ m : GL (Fin 2) ℝ,
      -((1 / 4 : ℂ) * deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.H t * archFlowMatrix ArchDir.H s)) 0) 0
          - (1 / 2 : ℂ) * deriv (fun t : ℝ => F (m * archFlowMatrix ArchDir.H t)) 0
          + deriv (fun t : ℝ => deriv (fun s : ℝ =>
            F (m * archFlowMatrix ArchDir.E t * archFlowMatrix ArchDir.Fm s)) 0) 0)
        = (1 / 4 - ν ^ 2) * F m) :
    (DifferentiableOn ℝ (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k₀ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (splitTorusGL2 (Real.log y / 2)) = 0) ∧
    (DifferentiableOn ℝ (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2))))
        (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)))) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k₀ : ℤ) : ℝ) : ℂ) * (y : ℂ)
                - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * F (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) = 0) := by sorry
