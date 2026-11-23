-- Prove2me | Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec
-- name    : GlobalTheory.AffinePointValues.specMap_appLE_fromSpec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:55.3928+00:00
-- url     : https://prove2.me/theorems/d3cb6180-9577-4ea1-89fe-be1f6700e7e2
-- title:
--   Affine Point Values: spec Map app LE from Spec
-- statement:
--   The Affine Point Values construction uses the spec Map app LE from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniquePointOfRingHom.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniquePointOfRingHom.lean#L23-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.AffinePointValues

theorem GlobalTheory.AffinePointValues.specMap_appLE_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (x : Spec R ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    Spec.map (x.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso R).hom) ≫ hV.fromSpec = x := by sorry
