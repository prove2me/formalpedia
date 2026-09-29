-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real
-- name    : LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e98a55ab-417e-50b6-a27b-2b3380c703d3
-- title:
--   Dual Γ-products and ε_∞ at three real places
-- statement:
--   Let $K$ be a number field, and let $w_0,w_1,w_2$ be infinite places of $K$, each real, pairwise distinct, such that every infinite place of $K$ equals one of them (so $K$ is totally real of degree $3$ and has no complex place). Let $uR$, $aR$ assign to each real place a complex number and an element of $\mathbf{Z}/2$, and let $uC$, $kC$ assign to each complex place a complex number and an integer. Let $P$ be a real archimedean parameter of principal type, $P = \mathrm{principal}\ \nu_1\ a_1\ \nu_2\ a_2$, and let $s \in \mathbf{C}$. Here `archOfParamR K P` and `archOfParamC K P` are the constant families sending every real place to $P$ and every complex place to its base change, and `RealArchParam.dual` sends $\mathrm{principal}\ \nu_1\ a_1\ \nu_2\ a_2$ to $\mathrm{principal}\ (-\nu_1)\ a_1\ (-\nu_2)\ a_2$, while `signShift` is $0$ on $0$ and $1$ on $1$, and `signEpsilon` is $1$ on $0$ and $i$ on $1$. Three assertions are made. First, the multiset `twistedGammaR`, the sum over real places of the `RealArchParam.gammaR` multiset of the `RealArchParam.twist` of $P^{\vee}$ by $(-uR\,w, aR\,w)$, mapped by $x \mapsto \Gamma_{\mathbf{R}}(s + 1/2 + x)$, has product equal to the explicit six-fold product of $\Gamma_{\mathbf{R}}\bigl(s + 1/2 + (-\nu_i - uR\,w) + \mathrm{signShift}(a_i + aR\,w)\bigr)$ for $i = 1,2$ and $w \in \{w_0,w_1,w_2\}$, in the bracketing displayed. Second, the corresponding `twistedGammaC` multiset, mapped by $x \mapsto \Gamma_{\mathbf{C}}(s + 1/2 + x)$, has product $1$. Third, `archRootNumber` of the constant families at the data $uR, aR, uC, kC$, multiplied by $(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}$ and by $(-1)$ raised to the number of complex places, equals $\prod_{w}\mathrm{signEpsilon}(a_1 + aR\,w)\,\mathrm{signEpsilon}(a_2 + aR\,w) \cdot (-1)^{(a_1+a_2).\mathrm{val}}$, the product over $w_0,w_1,w_2$ in the bracketing displayed.
--
--   This is the archimedean bookkeeping step for the dual side of a Rankin–Selberg pair over a totally real cubic field: it evaluates the dual $\Gamma_{\mathbf{R}}$-slot as an explicit product of six $\Gamma_{\mathbf{R}}$-factors, records that the $\Gamma_{\mathbf{C}}$-slot is trivial in the absence of complex places, and computes the archimedean root number with its two sign corrections as an explicit product of local sign factors. It is used by the torus-pair statements in the converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real.lean

import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real
    (K : Type) [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod =
        (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -uR w₀ h₀) + signShift (a₁ + aR w₀ h₀))) *
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -uR w₀ h₀) + signShift (a₂ + aR w₀ h₀)))) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -uR w₁ h₁) + signShift (a₁ + aR w₁ h₁))) *
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -uR w₁ h₁) + signShift (a₂ + aR w₁ h₁)))) *
        (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -uR w₂ h₂) + signShift (a₁ + aR w₂ h₂))) *
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -uR w₂ h₂) + signShift (a₂ + aR w₂ h₂)))))) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod = 1) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        (signEpsilon (a₁ + aR w₀ h₀) * signEpsilon (a₂ + aR w₀ h₀)) *
          ((signEpsilon (a₁ + aR w₁ h₁) * signEpsilon (a₂ + aR w₁ h₁)) *
          (signEpsilon (a₁ + aR w₂ h₂) * signEpsilon (a₂ + aR w₂ h₂))) *
          (-1 : ℂ) ^ (a₁ + a₂).val) := by sorry
