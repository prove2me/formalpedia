-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
-- name    : ModularCurve.FullLevel.ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/2f84329f-a6f0-5b51-82ed-1f0ebc59f184
-- title:
--   The q-scaled j-expansion is regular where j is
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$, and work inside the Laurent series field $\overline{\mathbb{Q}}((T))$. Let $\overline{F}_{M'} :=$ `modularFunctionFieldBar M'` be the intermediate field $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((T))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images under `coeffEmb` of the elements of `modularFunctionFieldFull M'` (itself the subfield of $\mathbb{Q}((T))$ generated over $\mathbb{Q}$ by `divisorExpansions M'`), and let $F :=$ `fieldBar q M'` be the analogous base change of `xHFunctionField (q^2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Assume $\overline{F}_{M'} \le F$. Let $J \in F$ be an element whose underlying Laurent series is `jqNModC (AlgebraicClosure ℚ) q`, that is, the image of the $q$-expansion $T^{-1}\cdot\mathrm{jNum}$ of $j$ over $\overline{\mathbb{Q}}$ under the exponent-scaling ring homomorphism `qExpand` with parameter $q$. Let $P$ be a place of $F$ over $\overline{\mathbb{Q}}$, i.e. a proper valuation subring of $F$ containing $\overline{\mathbb{Q}}$ and being a principal ideal ring, and write $P.\mathrm{ord}$ for the associated integer valuation. If $P.\mathrm{ord}$ is nonnegative on the element of $F$ obtained by including, along $\overline{F}_{M'} \le F$, the coefficientwise base change of $\mathrm{jq} = T^{-1}\cdot\mathrm{jNumQ} \in \mathbb{Q}((T))$, then $P.\mathrm{ord}(J) \ge 0$.
--
--   This is the statement that the $q$-scaled $j$-expansion has poles only where $j$ itself does: on the modular curve of level $\Gamma_H(q^2M')$ it expresses that the $j$-invariant of the $q$-isogenous elliptic curve is regular at every place where the $j$-invariant of the base curve is. It feeds the construction of semistable models and coverings of the full-level modular curve at the cusps and in the study of the inertia at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve

theorem ModularCurve.FullLevel.ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (J : ↥(fieldBar q M'))
    (hJ : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) q)
    (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
    (hP : 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) :
    0 ≤ P.ord (J : ↥(fieldBar q M')) := by sorry
