-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
-- name    : ModularCurve.exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/81056bdf-a3b4-5380-b683-d8ebc404d0bb
-- title:
--   Functions on the j-line with one pole and prescribed values
-- statement:
--   Let $k$ be a field, $S_0 \subseteq k$ a finite set, $c \in k$, $n \in \mathbb{N}$, and let $\varphi$ be an element of the level-one modular function field $F =$ `modularFunctionFieldC k 1`, the intermediate field of the Laurent series field $k(\!(q)\!)$ generated over $k$ by $\tilde\jmath =$ `jqModC k` (the image over $k$ of $q^{-1} E_4^3 \eta^{-24}$) together with its level-$1$ $q$-expansion rescaling, which is the same element. Places of $F$ over $k$ are valuation subrings of $F$ containing $k$, proper, and principal ideal rings; for such a place $v$ and $f \in F$, $\operatorname{ord}_v f$ is minus the logarithm of the associated adic valuation. Assume: (i) $\operatorname{ord}_v \varphi \ge 0$ for every place $v$ of $F$ other than the place obtained by transporting, along the $k$-isomorphism $k(X) \cong F$ sending $X$ to $\tilde\jmath$, the infinite place of $k(X)$; (ii) at that infinite place $\operatorname{ord} \varphi \ge -n$; (iii) for each $a \in S_0$, at the place transported from the place of $k(X)$ attached to $X - a$, the element $\varphi$ lies in the valuation subring and its residue equals the image of $c$ in the residue field. Then there is $Q \in k[X]$ such that $Q \ne 0$ implies $\deg Q + \#S_0 \le n$, and $\varphi = c + \bigl(\prod_{a \in S_0} (\tilde\jmath - a)\bigr) \cdot Q(\tilde\jmath)$, the polynomial being evaluated at $\tilde\jmath \in F$.
--
--   This is the genus-zero Riemann–Roch computation on the $\tilde\jmath$-line: a function regular away from the cusp is a polynomial in $\tilde\jmath$ of degree at most the pole order there, and agreeing with the constant $c$ at the points $a \in S_0$ forces divisibility of $\varphi - c$ by $\prod_{a \in S_0}(\tilde\jmath - a)$; the guard $Q \ne 0$ keeps the degree bound vacuous when $\varphi$ is constant. It is used by [`ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord`](thm.html#ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord), [`ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord`](thm.html#ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord) and [`ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal`](thm.html#ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal), where $S_0$ plays the role of a set of supersingular points on a component of a reduced modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue.lean

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
    {k : Type*} [Field k] [DecidableEq k] [DecidableEq (RatFunc k)] (S₀ : Finset k) (c : k) (n : ℕ)
    (φ : ↥(modularFunctionFieldC k 1))
    (hreg : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) → 0 ≤ v.ord φ)
    (hinf : -(n : ℤ) ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord φ)
    (hval : ∀ a ∈ S₀, (charLGeomPlaceOfPoint k a).HasValue φ c) :
    ∃ Q : Polynomial k, (Q ≠ 0 → Q.natDegree + S₀.card ≤ n) ∧
      φ = algebraMap k ↥(modularFunctionFieldC k 1) c
        + (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))
            - algebraMap k ↥(modularFunctionFieldC k 1) a))
          * Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by sorry
