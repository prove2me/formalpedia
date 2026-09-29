-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_three_real
-- name    : LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_three_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/de3e3f2d-0e11-5173-99b5-9462fa08fed7
-- title:
--   Discrete-series Γ-slots and root number, three real places
-- statement:
--   Let $K$ be a number field with exactly three infinite places, all real: places $w_0,w_1,w_2$ with `IsReal` witnesses $h_0,h_1,h_2$, pairwise distinct, and such that every infinite place of $K$ equals one of them. Let $uR,aR$ assign to each real place a complex number and an element of $\mathbb{Z}/2$, and $uC,kC$ assign to each complex place a complex number and an integer (these last two are vacuous data, as $K$ has no complex place). Let $P$ be a real archimedean parameter which is the discrete-series constructor `RealArchParam.discrete uP nP hnP` with $nP\ge 1$, take the constant families $archOfParamR\,P = P$ at real places and $archOfParamC\,P = P.baseChange$ at complex places, and let $s\in\mathbb{C}$. Five assertions are made. First, the multiset `twistedGammaR`, i.e. the sum over real places of `gammaR` of the twist of $P$ by $(uR(w),aR(w))$, has empty $\Gamma_{\mathbb{R}}$-product: the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over it is $1$. Second, the corresponding `twistedGammaC` multiset (real-place `gammaC` contributions plus complex-place ones) gives $$\prod_{j=0}^{2}\Gamma_{\mathbb{C}}\bigl(s+\tfrac12+(uP+uR(w_j))+\tfrac{nP}{2}\bigr).$$ Third and fourth are the same two identities for the dual data, the parameters replaced by `RealArchParam.dual` and `ComplexArchParam.dual` and the twisting data by $-uR$, $aR$, $-uC$, $-kC$: the $\Gamma_{\mathbb{R}}$-product is again $1$, and the $\Gamma_{\mathbb{C}}$-product is $\prod_{j=0}^{2}\Gamma_{\mathbb{C}}(s+\tfrac12+(-uP-uR(w_j))+\tfrac{nP}{2})$. Fifth, `archRootNumber` of these data, multiplied by $(-1)^{\mathrm{val}(P.centralSign)}$ and by $(-1)$ raised to the number of complex places, equals $i^{nP+1}\cdot\bigl(i^{nP+1}\cdot i^{nP+1}\bigr)\cdot(-1)^{nP+1}\cdot(-1)^{0}$.
--
--   This records, in the shape in which the converse-theorem machinery consumes it, the archimedean $\Gamma$-factors and root number of a discrete-series parameter twisted by local characters, base-changed constantly over the three real places of a totally real cubic field and over its (empty) set of complex places. It is used by the Rankin–Selberg unfolding statements that match unfolded and dual torus integrals against the expected $\Gamma$-factor in the discrete-series, three-real-place case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_three_real.lean

import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_three_real
    (K : Type) [Field K] [NumberField K]
    (w₀ w₁ w₂ : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂)
    (hall : ∀ w : NumberField.InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hP : P = RealArchParam.discrete uP nP hnP)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₁ h₁) + (nP : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₂ h₂) + (nP : ℂ) / 2)))) ∧
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₁ h₁) + (nP : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₂ h₂) + (nP : ℂ) / 2)))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        Complex.I ^ (nP + 1) * (Complex.I ^ (nP + 1) * Complex.I ^ (nP + 1)) *
          (-1 : ℂ) ^ (nP + 1) * (-1 : ℂ) ^ 0) := by sorry
