-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres
-- name    : GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:20.581556+00:00
-- url     : https://prove2.me/theorems/ad071256-0b01-4bbd-9324-18fb32850733
-- title:
--   Global Theory: flat of is Finite of finite Presentation of flat geometric fibres
-- statement:
--   The Global Theory construction uses the flat of is Finite of finite Presentation of flat geometric fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfIsFiniteOfFinitePresentationOfFlatGeometri.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfIsFiniteOfFinitePresentationOfFlatGeometri.lean#L150-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by sorry
