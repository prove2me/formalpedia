-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_jqNModC_mem_fieldBar
-- name    : ModularCurve.FullLevel.jqNModC_mem_fieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/9cb3fd68-169b-581c-85b1-600a6fdf3a3f
-- title:
--   j(q^q) lies in the level q²M' function field
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$. Consider the Laurent series field $\overline{\mathbb Q}((q))$ over the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$. The element in question is `jqNModC (AlgebraicClosure ℚ) q`, namely the image of the $j$-expansion $q^{-1} + \sum_{n\ge 0} c_n q^n$ (the Laurent series `jqModC`, built from the monomial $q^{-1}$ and the integral power series `jNum` pushed forward to $\overline{\mathbb Q}$) under the ring homomorphism `qExpand` of index $q$, which multiplies all exponents by $q$; informally, it is the series $j(q^q)$ obtained by the substitution $q \mapsto q^{q}$. The assertion is that this series belongs to `fieldBar q M'`, by definition `laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField (q ^ 2 * M') (levelH q M'))`: the intermediate field of $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ obtained by base change to $\overline{\mathbb Q}$ from the field `xHFunctionField` attached to level $q^2M'$ and the subgroup $H =$ `levelH q M'`, the kernel of the reduction map $(\mathbb Z/q^2M')^{\times} \to (\mathbb Z/q)^{\times}$, i.e. the units congruent to $1$ modulo $q$.
--
--   This records that the $j$-invariant of the $q$-isogenous curve, in the $\operatorname{diag}(q,1)$-conjugate model of the level structure, is a function on the curve of level $q^2M'$ for the subgroup of units trivial modulo $q$; it is the version of $j$ on which the later analysis of charts, poles and nodes at $q$ in the full-level setting is keyed. It is used by the statements producing charts, poles and nodal data over the level field in the Diamond part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_jqNModC_mem_fieldBar.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

theorem ModularCurve.FullLevel.jqNModC_mem_fieldBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M' := by sorry
