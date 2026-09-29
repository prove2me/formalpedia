-- Prove2me | Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
-- name    : NumberField.LevelArith.normal_levelField_of_isNormalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4b4ca3ee-cc4d-5bdc-a8fc-1af07a564537
-- title:
--   Normality of the level field under conjugation-stability
-- statement:
--   Let $K$ and $L$ be intermediate fields of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ is the algebraic closure `AlgebraicClosure ℚ`, both finite-dimensional over $\mathbb{Q}$, and suppose $K \le L$. Write $\Gamma_K$ and $\Gamma_L$ for the fixing subgroups of $K$ and of $L$ in the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, that is, the subgroups of automorphisms fixing $K$, respectively $L$, pointwise. The hypothesis `IsNormalLevel K L` is exactly the conjugation-stability condition that $g s g^{-1} \in \Gamma_L$ for all $g \in \Gamma_K$ and all $s \in \Gamma_L$. Under these hypotheses the conclusion is that `levelField K L hKL`, namely $L$ regarded via `IntermediateField.extendScalars` as an intermediate field of $\overline{\mathbb{Q}}$ over the base $K$, is a normal extension of $K$ in the sense of Mathlib's `Normal`: it is algebraic over $K$ and the minimal polynomial over $K$ of each of its elements splits in it.
--
--   This is the Galois-correspondence step identifying the normaliser condition on fixing subgroups with normality of the field extension $L/K$; it supplies the `Normal ↥K ↥(levelField K L hKL)` instance required by the level-arithmetic constructions over a pair $K \le L$, and is cited by the statements about $H^1$ of $S$-units, $S$-class groups and Kummer characters in that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith Pointwise

theorem NumberField.LevelArith.normal_levelField_of_isNormalLevel
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) (hnorm : IsNormalLevel K L) :
    Normal ↥K ↥(levelField K L hKL) := by sorry
