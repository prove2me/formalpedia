-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC
-- name    : ModularCurve.laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b89d5669-a8e1-5695-a2e4-cabb700594a3
-- title:
--   Base-changed compositum for Γ₁(M) and Γ_H(M)∩Γ₀(Mq)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $M$ be a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $q$ be a nonzero natural number. For a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ write $F(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set `intFormRatiosC ℚ Γ`, the $q$-expansion realisation of the function field of the modular curve of level $\Gamma$; and for an intermediate field $F_0$ of $\mathbb{Q}((q))$ write `laurentBaseChange L F₀` for the intermediate field of $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$ induced by the structure map $\mathbb{Q}\to L$. The assertion is an equality of intermediate fields of $L((q))$: the compositum (lattice join) of `laurentBaseChange L` applied to $F(\Gamma_1(M))$ and `laurentBaseChange L` applied to $F\bigl(\Gamma_H(M)\cap\Gamma_0(Mq)\bigr)$ equals `laurentBaseChange L` applied to $F\bigl(\Gamma_1(M)\cap\Gamma_0(Mq)\bigr)$. Here $\Gamma_H(M)$ is [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the upper-left-entry character `gamma0Units M` of $\Gamma_0(M)$, and the level $Mq$ group is $\Gamma_0(M\cdot q)$.
--
--   This is the function-field form of the statement that the degeneracy coverings $X_1(M)\cap X_0(Mq) \to X_1(M)$ and $X_H(M)\cap X_0(Mq) \to X_H(M)$ have matching degrees, so that the two smaller function fields already generate the larger one after base change to $L$. It is used in the comparison of Hecke and diamond operators on $X_H$-type curves with those on $X_1$ under pullback along the corresponding morphism of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XHHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.laurentBaseChange_x1FunctionField_sup_xHTopFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q] :
    ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) ⊔
        ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))
      = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * q)) := by sorry
