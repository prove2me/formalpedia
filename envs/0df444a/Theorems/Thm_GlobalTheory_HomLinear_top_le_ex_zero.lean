-- Prove2me | Theorems.Thm_GlobalTheory_HomLinear_top_le_ex_zero
-- name    : GlobalTheory.HomLinear.top_le_ex_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:35.67847+00:00
-- url     : https://prove2.me/theorems/0b788a0e-055c-4073-9590-97ac9c08dc1e
-- title:
--   Hom Linear: top le ex zero
-- statement:
--   The Hom Linear construction uses the top le ex zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsLinearOfIsMonHom.lean#L43-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem GlobalTheory.HomLinear.top_le_ex_zero (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by sorry
