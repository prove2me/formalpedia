-- Prove2me | Theorems.Thm_GlobalTheory_holUnif_linear_eq_self_of_ex_eq
-- name    : GlobalTheory.holUnif_linear_eq_self_of_ex_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:48.583213+00:00
-- url     : https://prove2.me/theorems/d10d1839-b9c3-4ae2-8fd7-9ab3000b1b23
-- title:
--   Global Theory: hol Unif linear eq self of ex eq
-- statement:
--   The Global Theory construction uses the hol Unif linear eq self of ex eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeAutOfIsomorphicThetaObjects.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLatticeAutOfIsomorphicThetaObjects.lean#L16-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLatticeAutOfIsomorphicThetaObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory

theorem GlobalTheory.holUnif_linear_eq_self_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z = z := by sorry
