-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
-- name    : LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0600fa2b-a09d-53de-a559-79919645ccf4
-- title:
--   Mellin transform of a weight-one Whittaker profile
-- statement:
--   Let $u_1,u_2\in\mathbb{C}$ with $u_1\neq u_2$, let $a_1,a_2\in\mathbb{Z}/2$ with $a_1\neq a_2$, let $W:\mathbb{C}\to\mathbb{C}$ and $f:\mathbb{R}\to\mathbb{C}$, and let $c\in\mathbb{C}$ be either $u_1-u_2$ or $u_2-u_1$. Assume $f$ is differentiable on $(0,\infty)$, that $f'$ is differentiable on $(0,\infty)$, that $f$ satisfies the Whittaker equation of weight one $y^2 f''(y)+\bigl(\tfrac14-\bigl(\tfrac{u_1-u_2}{2}\bigr)^2+2\pi y-4\pi^2y^2\bigr)f(y)=0$ for all $y>0$, that $\|f(y)\|\le Cy^N$ for all $y\ge 1$ for some real $C,N$, and that $f(y)\neq 0$ for some $y>0$. Assume further that for all $t>0$ one has $W(t)=(\sqrt t)^{\,u_1+u_2+1}f(t)$ and $c\,W(-t)=(\sqrt t)^{\,u_1+u_2+1}\bigl(2t f'(t)+(4\pi t-1)f(t)\bigr)$ (so $W$ enters only through its values at $\pm t$ with $t$ real). The conclusion asserts the existence of a real archimedean parameter $P'$, equal to the principal parameter $(u_1,a_1,u_2,a_2)$ or to $(u_1,a_2,u_2,a_1)$, and of $\rho\in\mathbb{C}^{\times}$, such that for every $b\in\mathbb{Z}/2$ and every $s$ with $\operatorname{Re} s>\max(-\operatorname{Re}u_1,-\operatorname{Re}u_2)$ the function $t\mapsto(\rho W(t)+(-1)^{b}\rho W(-t))/t$ is Mellin convergent at $s$ and its Mellin transform equals the archimedean factor of the twist of $P'$ by $(0,b)$, namely, writing $P'=(v_1,b_1,v_2,b_2)$, the product $\Gamma_{\mathbb{R}}\bigl(s+v_1+\mathrm{signShift}(b_1+b)\bigr)\,\Gamma_{\mathbb{R}}\bigl(s+v_2+\mathrm{signShift}(b_2+b)\bigr)$ (the complex part of the factor being an empty product for principal parameters).
--
--   This is the archimedean computation for a principal series of $\mathrm{GL}(2,\mathbb{R})$ of weight one: a moderately growing solution of the weight-one Whittaker equation with exponent $(u_1-u_2)/2$, together with its image under the lowering operator, produces torus profiles whose sign-symmetrised Mellin transforms are exactly the $\Gamma$-factors of the principal parameter and of its twists by $\mathrm{sgn}^{b}$. It supplies the archimedean input used in the converse-theorem and cubic-induction steps of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne.lean

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne (u₁ u₂ : ℂ)
    (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (W : ℂ → ℂ) (f : ℝ → ℂ) (c : ℂ)
    (hc : c = u₁ - u₂ ∨ c = u₂ - u₁)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f y ≠ 0)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t)
    (hWm : ∀ t : ℝ, 0 < t →
      c * W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (2 * (t : ℂ) * deriv f t + (4 * (π : ℂ) * (t : ℂ) - 1) * f t)) :
    ∃ P' : RealArchParam,
      (P' = RealArchParam.principal u₁ a₁ u₂ a₂ ∨ P' = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
            = (P'.twist 0 b).archFactor s := by sorry
