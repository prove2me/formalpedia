-- Prove2me | Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks
-- name    : GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:53:18.951543+00:00
-- url     : https://prove2.me/theorems/79b78761-7d6e-4f95-93b4-07f6912f1e4b
-- title:
--   Global Theory: is Iso stalk Map of flat of surjective On Stalks
-- statement:
--   The Global Theory construction uses the is Iso stalk Map of flat of surjective On Stalks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoStalkMapOfFlatOfSurjectiveOnStalks.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoStalkMapOfFlatOfSurjectiveOnStalks.lean#L95-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks {X U : Scheme.{0}} (j : U ⟶ X) [Flat j]
    [SurjectiveOnStalks j] (u : U) : IsIso (j.stalkMap u) := by sorry
