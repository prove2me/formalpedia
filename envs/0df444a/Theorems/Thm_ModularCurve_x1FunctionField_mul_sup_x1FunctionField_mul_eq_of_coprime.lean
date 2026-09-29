-- Prove2me | Theorems.Thm_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
-- name    : ModularCurve.x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f9594cd3-3d75-5437-9139-ce32539c4e8b
-- title:
--   Compositum of q-expansion fields of X₁(Ma) and X₁(Mb)
-- statement:
--   Let $M$, $a$, $b$ be natural numbers, each nonzero, with $3 \le M$ and $a$, $b$ coprime. For a natural number $N$, [`ModularCurve.x1FunctionField N`](def/ModularCurve_X1.html#L137) denotes [`ModularCurve.x1FunctionFieldC ℚ N`](def/ModularCurve_X1.html#L134), that is the intermediate field [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 N)`](def/ModularCurve_X1.html#L101) of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$, the $q$-expansion function field attached to the congruence subgroup $\Gamma_1(N)$ inside the Laurent series field over $\mathbb{Q}$. The assertion is an equality in the lattice of intermediate fields of $\mathbb{Q}((q))$ over $\mathbb{Q}$: the join (compositum) of [`ModularCurve.x1FunctionField (M * a)`](def/ModularCurve_X1.html#L137) and [`ModularCurve.x1FunctionField (M * b)`](def/ModularCurve_X1.html#L137) equals [`ModularCurve.x1FunctionField (M * a * b)`](def/ModularCurve_X1.html#L137). Thus the two $q$-expansion fields of levels $Ma$ and $Mb$ generate, inside $\mathbb{Q}((q))$, exactly the $q$-expansion field of level $Mab$. Both hypotheses enter: coprimality of $a$ and $b$, and $M \ge 3$, which rules out the contribution of $-1$ to the relevant groups.
--
--   This is the level-raising compatibility for the $q$-expansion function fields of the modular curves $X_1(N)$, reflecting the group-theoretic identity $\pm\Gamma_1(Ma) \cap \pm\Gamma_1(Mb) = \pm\Gamma_1(Mab)$ for coprime $a,b$ and $M \ge 3$, under the correspondence between composita of function fields and intersections of the corresponding subgroups. It feeds the base-changed form of the same statement, [`ModularCurve.laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq`](thm.html#ModularCurve.laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq), used in the analysis of the fields of modular functions of the curves $X_1(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.x1FunctionField_mul_sup_x1FunctionField_mul_eq_of_coprime
    (M a b : ℕ) [NeZero M] [NeZero a] [NeZero b] (hM : 3 ≤ M) (hab : Nat.Coprime a b) :
    ModularCurve.x1FunctionField (M * a) ⊔ ModularCurve.x1FunctionField (M * b) =
      ModularCurve.x1FunctionField (M * a * b) := by sorry
