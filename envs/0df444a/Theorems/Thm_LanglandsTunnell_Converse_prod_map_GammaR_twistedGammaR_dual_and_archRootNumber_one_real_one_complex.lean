-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
-- name    : LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/76de11ae-f94c-596a-93c2-4ad8148853e6
-- title:
--   Dual Γ-factors and archimedean root number in signature (1,1)
-- statement:
--   Let $K$ be a number field, $w_0$ a real infinite place of $K$ and $w_{\mathbb C}$ a complex one, and assume every infinite place of $K$ equals $w_{\mathbb C}$ or $w_0$. Let $u_R,a_R$ be families assigning to each real place a complex number and an element of $\mathbb Z/2$, and $u_{\mathbb C},k_{\mathbb C}$ families assigning to each complex place a complex number and an integer. Let $P$ be a real archimedean parameter with $P=\mathrm{principal}\,\nu_1\,a_1\,\nu_2\,a_2$, and let $s\in\mathbb C$. Writing $\mathrm{archOfParamR}$ and $\mathrm{archOfParamC}$ for the constant families with values $P$ and $P.\mathrm{baseChange}=\langle\nu_1,0,\nu_2,0\rangle$, three identities hold. First, the multiset `twistedGammaR` formed from the dual real parameters (so $\nu_i\mapsto-\nu_i$, signs unchanged), the negated family $-u_R$ and $a_R$ — that is, the sum over real places of the `gammaR` multiset of the twisted parameter — becomes, after applying $x\mapsto\Gamma_{\mathbb R}(s+\tfrac12+x)$ and taking the product, $\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12+(-\nu_i-u_R(w_0))+\mathrm{signShift}(a_i+a_R(w_0))\bigr)$, where $\mathrm{signShift}(a)$ is $0$ for $a=0$ and $1$ otherwise. Secondly, the corresponding `twistedGammaC` multiset, built from the dual real parameters and the dual of $P.\mathrm{baseChange}$ twisted by $-u_R,a_R$ and $-u_{\mathbb C},-k_{\mathbb C}$, has $\Gamma_{\mathbb C}$-product $\prod_{i=1,2}\Gamma_{\mathbb C}\bigl(s+\tfrac12+(-\nu_i-u_{\mathbb C}(w_{\mathbb C}))+|k_{\mathbb C}(w_{\mathbb C})|/2\bigr)$. Thirdly, `archRootNumber` at the untwisted families — the product over real places of the $\varepsilon$-factor of $P$ twisted by $(u_R,a_R)$ times the product over complex places of that of $P.\mathrm{baseChange}$ twisted by $(u_{\mathbb C},k_{\mathbb C})$ — multiplied by $(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}$ and by $(-1)^{\#\{\text{complex places}\}}$, equals $\epsilon(a_1+a_R(w_0))\,\epsilon(a_2+a_R(w_0))\cdot\bigl(i^{|k_{\mathbb C}(w_{\mathbb C})|}\bigr)^2\cdot(-1)^{(a_1+a_2).\mathrm{val}}\cdot(-1)^1$, with $\epsilon(0)=1$, $\epsilon(1)=i$.
--
--   This is the explicit evaluation, for a number field of signature $(1,1)$, of the archimedean $\Gamma$-multisets and root number attached to the contragredient of a principal archimedean parameter, in the form needed on the dual side of a functional equation. It is used by the Rankin–Selberg computations that identify a dual torus pair with the product of the archimedean root number, an explicit constant and a $\Gamma$-factor, for the discrete-series and weight-one profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex.lean

import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
    (K : Type) [Field K] [NumberField K]
    (w₀ wC : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : NumberField.InfinitePlace K, w = wC ∨ w = w₀)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod =
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -uR w₀ h₀) + signShift (a₁ + aR w₀ h₀))) *
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -uR w₀ h₀) + signShift (a₂ + aR w₀ h₀)))) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-ν₁ + -uC wC hC) + ((kC wC hC).natAbs : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-ν₂ + -uC wC hC) + ((kC wC hC).natAbs : ℂ) / 2))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        (signEpsilon (a₁ + aR w₀ h₀) * signEpsilon (a₂ + aR w₀ h₀)) *
          (Complex.I ^ (kC wC hC).natAbs * Complex.I ^ (kC wC hC).natAbs) *
          (-1 : ℂ) ^ (a₁ + a₂).val * (-1 : ℂ) ^ 1) := by sorry
