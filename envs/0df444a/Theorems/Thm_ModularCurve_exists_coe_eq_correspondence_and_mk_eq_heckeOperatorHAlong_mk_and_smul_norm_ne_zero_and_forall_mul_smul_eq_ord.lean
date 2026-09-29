-- Prove2me | Theorems.Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
-- name    : ModularCurve.exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/4e980d72-542b-514d-90ab-dcd3c3732ba7
-- title:
--   Root functions transport along the Hecke correspondence at ℓ
-- statement:
--   Fix a prime $p$, a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ and a prime $\ell$, and write $F_M = \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ for the base-changed function field `xHFunctionFieldBar M H` and $F'_\ell$ for the base change to $\overline{\mathbb{Q}}$ of the function field of level $\Gamma_H(M)\cap\Gamma_0(M\ell)$. Assume `HeckeDiamondInputsHAll M H`, i.e. that for every prime the degeneracy data `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ hold and that every $d \in (\mathbb{Z}/M)^{\times}$ is realised by an automorphism of $F_M/\overline{\mathbb{Q}}$ satisfying `IsDiamondAutHBar`. Let $w$ be a semilinear automorphism of $F_M$ (a pair consisting of a ring automorphism of $F_M$ and one of $\overline{\mathbb{Q}}$ compatible with the structure map), let $D$ be a divisor of degree zero on $F_M$, and let $f \neq 0$ satisfy $v(f) = p\,(w\cdot D)(v)$ at every place $v$. Then the two degeneracy maps $\alpha =$ `heckeAlphaHBar` (the inclusion $F_M \hookrightarrow F'_\ell$) and $\beta =$ `heckeBetaHBar` are integral, $F'_\ell$ has principal divisors, $F'_\ell$ is finite over $F_M$ along $\alpha$ and satisfies the pushforward norm formula along $\alpha$, and there is a degree-zero divisor $D_\ell$ with: $D_\ell = \alpha_{*}\beta^{*}D$ as divisors; the class of $D_\ell$ in $J_H$ equals `heckeOperatorHAlong` at $\ell$ applied to the class of $D$; the element $f_\ell = w\cdot N_{F'_\ell/F_M}\bigl(\beta(w^{-1}\cdot f)\bigr)$ is nonzero; and $v(f_\ell) = p\,(w\cdot D_\ell)(v)$ at every place $v$.
--
--   This is the step that propagates a $p$-divisibility relation $\operatorname{div} f = p\,(w\cdot D)$ on the modular curve $X_H(M)$ through the Hecke correspondence at an arbitrary prime $\ell$, simultaneously covering $T_\ell$ for $\ell \nmid M$ and $U_\ell$ for $\ell \mid M$, since both are given by the same correspondence $\alpha_{*}\beta^{*}$. It is used in the construction of reduced root functions attached to generators of the Hecke algebra acting on $J_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coe_eq_correspondence_and_mk_eq_heckeOperatorHAlong_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hin : HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
      (_ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfin)
      (D_ℓ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (D_ℓ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hβ hα
            (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (Pic0.mk D_ℓ : JH M H) = heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (Pic0.mk D) ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
       wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H)) ≠ 0) ∧
      ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (p : ℤ) * (wgen • (D_ℓ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v =
          v.ord (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
                 wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H))) := by sorry
