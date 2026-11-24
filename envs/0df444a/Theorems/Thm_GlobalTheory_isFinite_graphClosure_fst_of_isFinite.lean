-- Prove2me | Theorems.Thm_GlobalTheory_isFinite_graphClosure_fst_of_isFinite
-- name    : GlobalTheory.isFinite_graphClosure_fst_of_isFinite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:42.532956+00:00
-- url     : https://prove2.me/theorems/739be86b-f0b2-4185-8201-1c8f083ef81b
-- title:
--   Global Theory: is Finite graph Closure fst of is Finite
-- statement:
--   The Global Theory construction uses the is Finite graph Closure fst of is Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescOfIsFiniteOfDensePart.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescOfIsFiniteOfDensePart.lean#L17-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescOfIsFiniteOfDensePart
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory

theorem GlobalTheory.isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by sorry
