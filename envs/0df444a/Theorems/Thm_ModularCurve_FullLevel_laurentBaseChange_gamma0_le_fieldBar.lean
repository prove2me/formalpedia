-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar
-- name    : ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/188449d7-f595-5b1b-bcc1-bd3a01884abd
-- title:
--   Level-M' q-expansion field inside the full-level field
-- statement:
--   Let $q$ and $M'$ be natural numbers; no primality or positivity is assumed. Write $\overline{\mathbb{Q}}$ for `AlgebraicClosure ℚ`. On the left stands `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))`: inside $\mathbb{Q}((q))$ one forms the intermediate field generated over $\mathbb{Q}$ by all quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f/\mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where for some weight $k \in \mathbb{Z}$ the forms $f,g$ are modular of weight $k$ for the image of $\Gamma_0(M')$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f,p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$, and the denominator is non-zero; this field is then mapped coefficientwise into $\overline{\mathbb{Q}}((q))$ along $\mathbb{Q} \to \overline{\mathbb{Q}}$ and its image is adjoined to $\overline{\mathbb{Q}}$. On the right stands `fieldBar q M'`, that is the same base-change construction applied to `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. The assertion is the inclusion of the first intermediate field of $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$ in the second.
--
--   This records the degeneracy inclusion of function fields coming from $\Gamma_H(q^2M') \le \Gamma_0(q^2M') \le \Gamma_0(M')$, after adjoining $\overline{\mathbb{Q}}$-coefficients to the $q$-expansion fields. It is used by the full-level Tate-curve statements that compare linear maps on products of Tate modules with base-changed data, where the level-$M'$ field must be seen inside the full-level field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar (q M' : ℕ) :
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
      ModularCurve.FullLevel.fieldBar q M' := by sorry
