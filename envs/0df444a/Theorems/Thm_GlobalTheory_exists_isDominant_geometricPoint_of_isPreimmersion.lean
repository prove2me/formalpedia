-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDominant_geometricPoint_of_isPreimmersion
-- name    : GlobalTheory.exists_isDominant_geometricPoint_of_isPreimmersion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:46.30046+00:00
-- url     : https://prove2.me/theorems/96b40862-cc89-4a61-bc45-219bff48a292
-- title:
--   Global Theory: exists is Dominant geometric Point of is Preimmersion
-- statement:
--   The Global Theory construction uses the exists is Dominant geometric Point of is Preimmersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L15-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
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

theorem GlobalTheory.exists_isDominant_geometricPoint_of_isPreimmersion {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by sorry
