-- Prove2me | Theorems.Thm_GlobalTheory_injective_of_finiteType_int_of_charZero
-- name    : GlobalTheory.injective_of_finiteType_int_of_charZero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:55.920317+00:00
-- url     : https://prove2.me/theorems/c2d882fb-28fb-44ba-aa99-d12bf37264ee
-- title:
--   Global Theory: injective of finite Type int of char Zero
-- statement:
--   The Global Theory construction uses the injective of finite Type int of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRingHomComplexCompEqOfCountable.lean#L62-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRingHomComplexCompEqOfCountable.lean#L62-L80

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

theorem GlobalTheory.injective_of_finiteType_int_of_charZero {o K : Type} [CommRing o] [IsDomain o]
    [Ring.DimensionLEOne o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K] (β : o →+* K) :
    Function.Injective β := by sorry
