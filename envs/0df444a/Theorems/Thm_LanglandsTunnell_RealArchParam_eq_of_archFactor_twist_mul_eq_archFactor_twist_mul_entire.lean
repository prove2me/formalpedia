-- Prove2me | Theorems.Thm_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
-- name    : LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/72d2cb21-04a9-52c9-8414-0f4cac304fad
-- title:
--   Entire ratio of archimedean factors forces the signs to agree
-- statement:
--   Let $u_1,u_2$ be complex numbers and $a_1,a_2\in\mathbb{Z}/2$, with $a_1\neq a_2$, $u_1\neq u_2$ and $|\operatorname{Re}(u_1-u_2)|<1$. Let $P'$ be a `RealArchParam` which is either `principal` $u_1\,a_1\,u_2\,a_2$ or its sign-swap `principal` $u_1\,a_2\,u_2\,a_1$. Let $\rho\neq 0$ be a complex number, let $\Phi:\mathbb{C}\to\mathbb{C}$ be entire (differentiable on all of $\mathbb{C}$), and let $\sigma_0$ be real. Assume that for every $s$ with $\operatorname{Re} s>\sigma_0$ one has $\rho\cdot\mathrm{archFactor}(P'.\mathrm{twist}\,0\,0)(s)=\mathrm{archFactor}((\mathrm{principal}\,u_1\,a_1\,u_2\,a_2).\mathrm{twist}\,0\,0)(s)\cdot\Phi(s)$. Here twisting by $(0,0)$ leaves a principal parameter unchanged, and for a principal parameter the archimedean factor is $\mathrm{archFactor}(s)=\Gamma_{\mathbb{R}}\bigl(s+(u_1+\mathrm{signShift}\,a_1)\bigr)\,\Gamma_{\mathbb{R}}\bigl(s+(u_2+\mathrm{signShift}\,a_2)\bigr)$, the multiset `gammaC` being empty, where `signShift` attaches to a class in $\mathbb{Z}/2$ the corresponding shift. The conclusion is that $P'$ equals `principal` $u_1\,a_1\,u_2\,a_2$, i.e. the sign-swapped alternative is excluded.
--
--   This is the archimedean rigidity step which shows that a non-zero multiple of the archimedean $L$-factor of a real principal parameter can be divided by the factor of another principal parameter with the same exponents but interchanged sign characters only if the two parameters coincide; the exclusion rests on the poles of the $\Gamma_{\mathbb{R}}$-factors. It is used in the Langlands–Tunnell part of the development, in the identification of the archimedean component of the weight-one automorphic datum produced by cubic induction and in the Whittaker/Casimir-eigenvector constructions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire.lean

import Definitions.Def_LanglandsTunnell_ArchParam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (htype : |(u₁ - u₂).re| < 1)
    (P' : RealArchParam) (hP' : P' = .principal u₁ a₁ u₂ a₂ ∨ P' = .principal u₁ a₂ u₂ a₁)
    (ρ : ℂ) (hρ : ρ ≠ 0) (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      ρ * (P'.twist 0 0).archFactor s = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 0).archFactor s * Φ s) :
    P' = .principal u₁ a₁ u₂ a₂ := by sorry
