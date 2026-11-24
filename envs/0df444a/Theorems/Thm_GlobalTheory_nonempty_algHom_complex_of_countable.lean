-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_algHom_complex_of_countable
-- name    : GlobalTheory.nonempty_algHom_complex_of_countable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:00.704192+00:00
-- url     : https://prove2.me/theorems/068e0a6d-a01c-4604-8475-518949043a48
-- title:
--   Global Theory: nonempty alg Hom complex of countable
-- statement:
--   The Global Theory construction uses the nonempty alg Hom complex of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRingHomComplexCompEqOfCountable.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRingHomComplexCompEqOfCountable.lean#L14-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRingHomComplexCompEqOfCountable
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

theorem GlobalTheory.nonempty_algHom_complex_of_countable (R K : Type) [CommRing R] [IsDomain R] [Countable R]
    [Field K] [Countable K] [Algebra R K] [Algebra R ℂ] [FaithfulSMul R K] [FaithfulSMul R ℂ] :
    Nonempty (K →ₐ[R] ℂ) := by sorry
