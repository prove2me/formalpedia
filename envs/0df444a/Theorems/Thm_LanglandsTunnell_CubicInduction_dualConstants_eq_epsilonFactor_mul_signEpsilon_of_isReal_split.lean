-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
-- name    : LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/998c5be5-a700-5c4a-ade7-4b074df171aa
-- title:
--   Archimedean epsilon constants at three real places
-- statement:
--   Let $K$ be a number field, and suppose given data at its infinite places: complex numbers $uR_w$ and classes $aR_w \in \mathbb{Z}/2$ for each real place $w$, and integers $kC_w$ for each complex place $w$. Let $w_0, w_1, w_2$ be real infinite places of $K$, pairwise distinct, and assume every infinite place of $K$ equals one of $w_0$, $w_1$, $w_2$ (so $K$ is totally real of degree $3$). Let $t \in \mathbb{C}$ and $e \in \mathbb{Z}$. Form the principal real archimedean parameter with data $(uR_{w_1}, aR_{w_1}, uR_{w_2}, aR_{w_2})$ and twist it by $(t, e \bmod 2)$, which adds $t$ to both complex entries and $e \bmod 2$ to both $\mathbb{Z}/2$ entries; its epsilon factor is by definition the product of the two sign constants, where $\mathrm{signEpsilon}(a)$ is $1$ for $a = 0$ and $i$ otherwise. The assertion is that this epsilon factor, multiplied by $\mathrm{signEpsilon}(aR_{w_0} + e \bmod 2)$, equals the product over all real places $w$ of $\mathrm{signEpsilon}(aR_w + e \bmod 2)$, times the product over all complex places $w$ of $i^{|kC_w|}$, times $\prod_w \lambda_{\mathrm{arch}}(w)$, where $\lambda_{\mathrm{arch}}(w)$ is $1$ at real $w$ and $\mathrm{signEpsilon}(1) = i$ at complex $w$.
--
--   This is a bookkeeping identity matching the archimedean epsilon constant attached to a twisted split parameter at two real places, together with the sign at a third real place, against the global archimedean constant assembled place by place. It feeds the cubic-induction step, being used in [`LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq`](thm.html#LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split.lean

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArchEpsilon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (w₁ : InfinitePlace K) (h₁ : w₁.IsReal)
    (w₂ : InfinitePlace K) (h₂ : w₂.IsReal)
    (h₀₁ : w₀ ≠ w₁) (h₀₂ : w₀ ≠ w₂) (h₁₂ : w₁ ≠ w₂)
    (hplaces : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (t : ℂ) (e : ℤ) :
    ((RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)).twist t (e : ZMod 2)).epsilonFactor *
        signEpsilon (aR w₀ h₀ + (e : ZMod 2)) =
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
          fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
            fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
        ∏ w : InfinitePlace K, lambdaArch K w := by sorry
