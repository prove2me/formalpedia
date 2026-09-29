-- Prove2me | Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
-- name    : ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/1d38727f-d6d7-5b20-b159-e2574c6963dd
-- title:
--   Inertia degree one along maps into L·ℚ(X(Γ))
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, given as a $\mathbb{Q}$-algebra, and let $F$ be any field that is an $L$-algebra. Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ equal to [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) $\mathbb{Q}\,\Gamma$, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of $q$-expansion series attached to pairs of modular forms for $\Gamma$ (of any weight) admitting integral power-series $q$-expansions, the denominator series being nonzero. Write $F' =$ [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) $L\,F_0$ for the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Let $\varphi : F \to F'$ be an $L$-algebra homomorphism whose underlying ring homomorphism is integral, and let $W$ be a place of $F'$ over $L$, that is, a valuation subring of $F'$ containing the image of $L$, distinct from $F'$ itself and a principal ideal ring. Then the inertia degree of $W$ along $\varphi$ is $1$: the residue field of $W$ has degree $1$ over the residue field of the valuation subring of $F$ obtained by restricting $W$ along $\varphi$.
--
--   This is the residue-degree statement accompanying the fact that every place of the function field of $X(\Gamma)$ over an algebraically closed field has degree one; the shape here is source-generic, covering an arbitrary integral $L$-algebra map into that function field, as arises for degeneracy and Hecke correspondences $X(\Gamma') \to X(\Gamma)$. It is used in the divisor computations at a point for Hecke and specialization arguments, for instance in the analysis of pushforwards and fibres of places along such maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
    {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (φ : F →ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀))
    (hφ : φ.toRingHom.IsIntegral)
    (W : AlgebraicCurve.Place L ↥(ModularCurve.laurentBaseChange L F₀)) :
    W.inertiaDegAlong φ hφ = 1 := by sorry
