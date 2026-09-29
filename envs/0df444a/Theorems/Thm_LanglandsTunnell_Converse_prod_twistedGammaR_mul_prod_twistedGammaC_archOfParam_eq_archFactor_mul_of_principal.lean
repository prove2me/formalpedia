-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
-- name    : LanglandsTunnell.Converse.prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/d401cf7a-9a9c-5e03-affc-2c7e6ef5b3bd
-- title:
--   Archimedean Γ-factor splitting for a cubic field, principal case
-- statement:
--   Let $K$ be a number field and fix archimedean twisting data: numbers $u^{\mathbb R}_w\in\mathbb C$ and signs $a_w\in\mathbb Z/2$ for every real place $w$, and numbers $u^{\mathbb C}_w\in\mathbb C$ and integers $k_w$ for every complex place $w$. Let $w_0$ be a real place of $K$, and let $P_2$ be a real archimedean parameter satisfying one of two alternatives: either there are real places $w_1,w_2$ with $w_0,w_1,w_2$ pairwise distinct and every infinite place of $K$ equal to one of the three, and $P_2=\mathtt{principal}\,(u^{\mathbb R}_{w_1})(a_{w_1})(u^{\mathbb R}_{w_2})(a_{w_2})$; or there is a complex place $w_C$ such that every infinite place equals $w_C$ or $w_0$, and either $k_{w_C}\neq0$ and $P_2=\mathtt{discrete}\,(u^{\mathbb C}_{w_C})\,|k_{w_C}|$, or $k_{w_C}=0$ and $P_2=\mathtt{principal}\,(u^{\mathbb C}_{w_C})\,0\,(u^{\mathbb C}_{w_C})\,1$. Let $P=\mathtt{principal}\,\nu_1\,a_1\,\nu_2\,a_2$. Then for every $s\in\mathbb C$ the following identity holds. On the left, `archOfParamR` and `archOfParamC` assign $P$ to each real place and its base change $\langle\nu_1,0,\nu_2,0\rangle$ to each complex place; one forms the multiset $\sum_{w\ \mathrm{real}}\mathrm{gammaR}(P.\mathrm{twist}(u^{\mathbb R}_w,a_w))$ and takes the product of $\Gamma_{\mathbb R}(s+x)$ over it, times the product of $\Gamma_{\mathbb C}(s+y)$ over $\sum_{w\ \mathrm{real}}\mathrm{gammaC}(P.\mathrm{twist}(u^{\mathbb R}_w,a_w))+\sum_{w\ \mathrm{complex}}\mathrm{gammaC}\big(\langle\nu_1,0,\nu_2,0\rangle.\mathrm{twist}(u^{\mathbb C}_w,k_w)\big)$. Here the twist of a principal parameter adds $u$ to both exponents and $a$ to both signs, $\mathrm{gammaR}$ of a principal parameter is the two-element multiset of its exponents shifted by `signShift` of its signs, and its $\mathrm{gammaC}$ is empty. This product equals $\mathrm{archFactor}(P.\mathrm{twist}(u^{\mathbb R}_{w_0},a_{w_0}),s)\cdot\mathrm{archFactor}(P_2.\mathrm{twist}(\nu_1,a_1),s)\cdot\mathrm{archFactor}(P_2.\mathrm{twist}(\nu_2,a_2),s)$.
--
--   This is the archimedean bookkeeping identity for an induced $GL_3\times GL_2$ pair over a field with the signature of a cubic field: the full twisted product of $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-factors factors as the local factor at the marked real place $w_0$ times the two character twists of the parameter carried by the remaining infinite places, in the case where the $GL_2$-parameter is principal. It feeds the Rankin–Selberg computations of unfolded torus pairs used as input to the converse theorem in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal.lean

import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.prod_twistedGammaR_mul_prod_twistedGammaC_archOfParam_eq_archFactor_mul_of_principal
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    ((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + x)).prod *
        ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
          fun x => Complex.Gammaℂ (s + x)).prod =
      (P.twist (uR w₀ h₀) (aR w₀ h₀)).archFactor s *
        ((P₂.twist ν₁ a₁).archFactor s * (P₂.twist ν₂ a₂).archFactor s) := by sorry
