-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
-- name    : ModularCurve.finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/d56581c0-5133-56e9-8c0e-d24c21066309
-- title:
--   Riemann–Roch spaces of K·ℚ(X₁(M)) are finite-dimensional
-- statement:
--   Let $K$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure, and let $M$ be a nonzero natural number. Write $F_\mathbb{Q}$ for `qExpFunctionFieldC ℚ (Gamma1 M)`, the intermediate field of the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$ generated over $\mathbb{Q}$ by all quotients $\iota(p_f)/\iota(p_g)$ of Laurent series attached to integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ of modular forms $f,g$ of some weight $k$ for $\Gamma_1(M)$ (with $\iota(p_g)\neq 0$), and let $F_K$ be `laurentBaseChange K F_\mathbb{Q}`, the intermediate field of $K((q))$ generated over $K$ by the image of $F_\mathbb{Q}$ under the coefficientwise map $\mathbb{Q}((q))\to K((q))$ induced by $\mathbb{Q}\to K$. Let $D$ be a divisor of $F_K$ over $K$, i.e. a finitely supported $\mathbb{Z}$-valued function on the set of places of $F_K/K$, a place being a valuation subring of $F_K$ that contains the image of $K$, is not all of $F_K$, and is a principal ideal ring. Then the Riemann–Roch space $L(D)$, the $K$-submodule of those $f\in F_K$ with $v(f)\le \exp(D(v))$ in $\mathbb{Z}^{m0}$ for every place $v$, where $v$ denotes the associated adic valuation, is finite-dimensional over $K$.
--
--   This is the finiteness half of the Riemann–Roch theory for the function field $K\cdot\mathbb{Q}(X_1(M))$ of the modular curve $X_1(M)$ over an algebraically closed field of characteristic zero. It supplies the finite-dimensionality needed to extract a basis of $L(D)$ when lower bounds for $\dim_K M_{2m}(\Gamma_1(M))$ are proved, and is cited in both the even and odd weight cases of the dimension estimate for modular forms on $\Gamma_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (D : AlgebraicCurve.Divisor K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace D) := by sorry
