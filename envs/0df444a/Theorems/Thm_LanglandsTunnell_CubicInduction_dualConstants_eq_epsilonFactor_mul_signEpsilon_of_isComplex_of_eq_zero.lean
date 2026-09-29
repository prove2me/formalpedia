-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_eq_zero
-- name    : LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/74402a75-d15a-575f-a078-5390edccf0fb
-- title:
--   Archimedean constants for one real and one complex place, exponent zero
-- statement:
--   Let $K$ be a number field equipped with data at its infinite places: a function $a_R$ assigning to each real place $w$ (with a proof that $w$ is real) an element of $\mathbb{Z}/2$, and functions $u_C$, $k_C$ assigning to each complex place a complex number and an integer respectively. Suppose given a complex place $w_C$ of $K$, a real place $w_0$ of $K$, and the hypothesis that every infinite place of $K$ equals $w_C$ or $w_0$; suppose further that $k_C(w_C)=0$. Let $t\in\mathbb{C}$ and $e\in\mathbb{Z}$. Consider the real archimedean parameter `RealArchParam.principal` with data $(u_C(w_C),0,u_C(w_C),1)$ and its twist by $(t, e \bmod 2)$, namely `principal` with data $(u_C(w_C)+t,\,0+e,\,u_C(w_C)+t,\,1+e)$; its `epsilonFactor` is the product of the two sign constants of its $\mathbb{Z}/2$-entries, where `signEpsilon` sends $0$ to $1$ and the nonzero class to $i$. The assertion is that this epsilon factor, multiplied by `signEpsilon`$(a_R(w_0)+e)$, equals the product over all real places $w$ of `signEpsilon`$(a_R(w)+e)$, times the product over all complex places $w$ of $i^{|k_C(w)|}$, times the product over all infinite places $w$ of $\lambda$-constants `lambdaArch K w`, the latter being $1$ at a real place and `signEpsilon 1` $= i$ at a complex place.
--
--   This is the archimedean root-number bookkeeping identity in the case of a field with exactly one real and one complex infinite place (a cubic signature) and vanishing exponent at the complex place: it matches the epsilon factor of a twisted split parameter of $\mathrm{GL}_2(\mathbb{R})$ against the global product of local archimedean constants. It is used by [`LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq`](thm.html#LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq) in the archimedean part of the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArchEpsilon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isComplex_of_eq_zero
    (K : Type) [Field K] [NumberField K]
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (wC : InfinitePlace K) (hC : wC.IsComplex) (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (hplaces : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (hk : kC wC hC = 0) (t : ℂ) (e : ℤ) :
    ((RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1).twist t (e : ZMod 2)).epsilonFactor *
        signEpsilon (aR w₀ h₀ + (e : ZMod 2)) =
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
          fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
            fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
        ∏ w : InfinitePlace K, lambdaArch K w := by sorry
