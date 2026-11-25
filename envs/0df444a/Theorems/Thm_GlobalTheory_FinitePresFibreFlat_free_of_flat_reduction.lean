-- Prove2me | Theorems.Thm_GlobalTheory_FinitePresFibreFlat_free_of_flat_reduction
-- name    : GlobalTheory.FinitePresFibreFlat.free_of_flat_reduction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:36.366399+00:00
-- url     : https://prove2.me/theorems/809fa52d-0cae-4a86-9e58-de8fe2335a00
-- title:
--   Finite Pres Fibre Flat: free of flat reduction
-- statement:
--   The Finite Pres Fibre Flat construction uses the free of flat reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfIsFiniteOfFinitePresentationOfFlatGeometri.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FlatOfIsFiniteOfFinitePresentationOfFlatGeometri.lean#L21-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_free_of_flat_reduction

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
open GlobalTheory.FinitePresFibreFlat
open TensorProduct IsLocalRing FiniteFibreFlat

theorem GlobalTheory.FinitePresFibreFlat.free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by sorry
