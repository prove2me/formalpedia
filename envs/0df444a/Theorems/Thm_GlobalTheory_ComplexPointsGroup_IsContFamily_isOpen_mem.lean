-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPointsGroup_IsContFamily_isOpen_mem
-- name    : GlobalTheory.ComplexPointsGroup.IsContFamily.isOpen_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:55.724777+00:00
-- url     : https://prove2.me/theorems/39a5bec7-5388-422d-b2c5-d702cce8af62
-- title:
--   Is Cont Family: is Open mem
-- statement:
--   The Is Cont Family construction uses the is Open mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsTopologicalGroupComplexPoints.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsTopologicalGroupComplexPoints.lean#L16-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]

theorem GlobalTheory.ComplexPointsGroup.IsContFamily.isOpen_mem {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens) :
    IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U} := by sorry
