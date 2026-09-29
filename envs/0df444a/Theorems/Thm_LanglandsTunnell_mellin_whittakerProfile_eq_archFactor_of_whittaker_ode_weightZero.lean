-- Prove2me | Theorems.Thm_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero
-- name    : LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b263b604-8804-5365-aefe-fe2866f00a6a
-- title:
--   Mellin transforms of the weight-zero and weight-two torus profiles
-- statement:
--   Let $u_1,u_2\in\mathbb{C}$, let $a\in\mathbb{Z}/2$, let $W_0,W_2:\mathbb{C}\to\mathbb{C}$ and let $f_0:\mathbb{R}\to\mathbb{C}$. Assume $f_0$ is differentiable on $(0,\infty)$, that $\operatorname{deriv} f_0$ is again differentiable there, that for every $y>0$ one has $y^2 f_0''(y)+\bigl(\tfrac14-((u_1-u_2)/2)^2-4\pi^2y^2\bigr)f_0(y)=0$, that $\|f_0(y)\|\le C y^N$ for all $y\ge 1$ for some real $C,N$, and that $f_0(y)\neq0$ for at least one $y>0$. Assume further that for all $t>0$: $W_0(t)=(\sqrt t)^{u_1+u_2+1}f_0(t)$; $W_0(-t)=(\sqrt t)^{u_1+u_2+1}(-1)^{a}f_0(t)$; $W_2(t)=(\sqrt t)^{u_1+u_2+1}\cdot(-\tfrac1{4\pi})\bigl(2t f_0'(t)-4\pi t f_0(t)\bigr)$; and $W_2(-t)=(\sqrt t)^{u_1+u_2+1}\cdot(-\tfrac1{4\pi})(-1)^{a}\bigl(2t f_0'(t)+4\pi t f_0(t)\bigr)$, exponents $(-1)^a$ meaning $(-1)^{a.\mathrm{val}}$. Then there is $\rho\neq0$ such that for every $s$ with $\operatorname{Re} s>\max(-\operatorname{Re}u_1,-\operatorname{Re}u_2)$ the three functions $t\mapsto\bigl(\rho W_0(t)+(-1)^{a}\rho W_0(-t)\bigr)/t$, $t\mapsto\bigl(\rho W_2(t)+(-1)^{a}\rho W_2(-t)\bigr)/t$ and $t\mapsto\bigl(\rho W_2(t)+(-1)^{a+1}\rho W_2(-t)\bigr)/t$ satisfy `MellinConvergent` at $s$, with Mellin transforms respectively $A(s)$, $\frac{2s+u_1+u_2-1}{4\pi}A(s)$ and $B(s)$, where, with $P$ the principal parameter $(u_1,a,u_2,a)$, $A(s)$ is the archimedean factor of $P$ twisted by $(0,a)$, i.e. $\Gamma_{\mathbb{R}}(s+u_1+\mathrm{signShift}(a+a))\Gamma_{\mathbb{R}}(s+u_2+\mathrm{signShift}(a+a))$, and $B(s)$ that of $P$ twisted by $(0,a+1)$, i.e. the same product with $\mathrm{signShift}(a+a+1)$ in place of $\mathrm{signShift}(a+a)$ (in $\mathbb{Z}/2$, $a+a=0$ and $a+a+1=1$).
--
--   This is the archimedean Whittaker computation for the weight-zero principal series of $GL_2(\mathbb{R})$: any moderately growing nonzero solution of Whittaker's equation with spectral parameter $(u_1-u_2)/2$ and weight $0$ produces, after normalisation by a single nonzero scalar $\rho$, torus profiles in weights $0$ and $2$ whose Mellin transforms are exactly the Gamma factors of the principal parameter $(u_1,a,u_2,a)$ twisted by the sign character, the weight-two profile in the same parity contributing the extra factor $(2s+u_1+u_2-1)/(4\pi)$. It is used in the construction of archimedean Whittaker data from Casimir eigenvectors of minimal weight and in the converse-theorem and cubic-induction steps that compare such data with the principal-series parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero.lean

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero (u₁ u₂ : ℂ)
    (a : ZMod 2) (W₀ W₂ : ℂ → ℂ) (f₀ : ℝ → ℂ)
    (hf₀ : DifferentiableOn ℝ f₀ (Set.Ioi 0)) (hf₀' : DifferentiableOn ℝ (deriv f₀) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f₀) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f₀ y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f₀ y ≠ 0)
    (hW0p : ∀ t : ℝ, 0 < t → W₀ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f₀ t)
    (hW0m : ∀ t : ℝ, 0 < t →
      W₀ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * ((-1 : ℂ) ^ a.val * f₀ t))
    (hW2p : ∀ t : ℝ, 0 < t →
      W₂ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * (2 * (t : ℂ) * deriv f₀ t - 4 * (π : ℂ) * (t : ℂ) * f₀ t)))
    (hW2m : ∀ t : ℝ, 0 < t →
      W₂ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * ((-1 : ℂ) ^ a.val * (2 * (t : ℂ) * deriv f₀ t + 4 * (π : ℂ) * (t : ℂ) * f₀ t)))) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                * ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s) := by sorry
