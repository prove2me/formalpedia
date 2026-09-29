-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
-- name    : NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8a4f940b-6427-5313-9132-3368e271618e
-- title:
--   Strong approximation for GL₂/ℚ at finite level K₁(N)
-- statement:
--   Let $N$ be a nonzero ideal of the ring of integers of $\mathbb{Q}$ (so $N \neq \bot$), and let $g$ be an element of the general linear group $\mathrm{GL}_2$ over the finite adele ring of $\mathbb{Q}$, formed with respect to its ring of integers. The assertion is that there exists $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ such that, writing $\gamma$ first for its diagonal image in $\mathrm{GL}_2$ of the full adele ring under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) (the entrywise structure map $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$) and then for the image of that under `glFin` (the entrywise projection of the adele ring onto its finite part, `adeleFin`), the product `glFin (globalPoints γ) * g` lies in the subgroup `finiteLevelOne` of level $N$. Membership in this subgroup means that both the matrix of that product and the matrix of its inverse satisfy the predicate `IsLevelOneMatrix` for $N$, i.e. they satisfy the predicate `IsLevelZeroMatrix` for $N$ and in addition their lower-right entry $m_{11}$ satisfies $m_{11} - 1 \in$ `idealBall` of $N$.
--
--   This is strong approximation for $\mathrm{GL}_2$ over $\mathbb{Q}$ in the form $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{f}) = \mathrm{GL}_2(\mathbb{Q}) \cdot K_1(N)$, refining the maximal-compact case $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{f}) = \mathrm{GL}_2(\mathbb{Q}) \cdot \mathrm{GL}_2(\widehat{\mathbb{Z}})$ to the level subgroup attached to a nonzero ideal $N$. It is used in the passage between classical cusp forms for $\Gamma_1(N)$ and their adelic lifts, and in the corresponding statement for the full adelic level-one group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N := by sorry
