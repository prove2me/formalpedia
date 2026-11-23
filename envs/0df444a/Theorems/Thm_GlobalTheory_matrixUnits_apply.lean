-- Prove2me | Theorems.Thm_GlobalTheory_matrixUnits_apply
-- name    : GlobalTheory.matrixUnits_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:13.23869+00:00
-- url     : https://prove2.me/theorems/7770810e-3e9f-4ea2-abfa-d7daa569cb59
-- title:
--   Global Theory: matrix Units apply
-- statement:
--   The Global Theory construction uses the matrix Units apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L40-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L40-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
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
open GlobalTheory

theorem GlobalTheory.matrixUnits_apply {La : Type} [AddCommGroup La]
    (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La) :
    (∀ u v x, r (Matrix.single 0 u 1) (r (Matrix.single v 0 1) x) =
      if u = v then r (Matrix.single 0 0 1) x else 0) ∧
    (∀ x, ∑ u, r (Matrix.single u 0 1) (r (Matrix.single 0 u 1) x) = x) ∧
    (∀ x, r (Matrix.single 0 0 1) (r (Matrix.single 0 0 1) x) = r (Matrix.single 0 0 1) x) := by sorry
