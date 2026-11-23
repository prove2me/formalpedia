-- Prove2me | Theorems.Thm_GlobalTheory_PowLie_isTangent_iff
-- name    : GlobalTheory.PowLie.isTangent_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:56.7279+00:00
-- url     : https://prove2.me/theorems/b0e6883d-3870-44ea-8596-9f74ba3d66db
-- title:
--   Pow Lie: is Tangent iff
-- statement:
--   The Pow Lie construction uses the is Tangent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieCombIffProd.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieCombIffProd.lean#L33-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowLie
variable {R : Type} [CommRing R]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem GlobalTheory.PowLie.isTangent_iff {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G]
    (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w ↔ _root_.GlobalTheory.PowLie.zeroPt R ≫ w = η[G] := by sorry
