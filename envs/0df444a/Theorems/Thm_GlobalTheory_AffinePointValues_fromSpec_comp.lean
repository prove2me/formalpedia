-- Prove2me | Theorems.Thm_GlobalTheory_AffinePointValues_fromSpec_comp
-- name    : GlobalTheory.AffinePointValues.fromSpec_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:57.097638+00:00
-- url     : https://prove2.me/theorems/dd7fb9b2-c34f-4751-b270-1b15add78132
-- title:
--   Affine Point Values: from Spec comp
-- statement:
--   The Affine Point Values construction uses the from Spec comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniquePointOfRingHom.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsUniquePointOfRingHom.lean#L30-L34

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

theorem GlobalTheory.AffinePointValues.fromSpec_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (s : Y ⟶ Spec R) (h) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appLE ⊤ V h) := by sorry
