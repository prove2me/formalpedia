-- Prove2me | Theorems.Thm_GlobalTheory_NormCurve_finite_integralClosure
-- name    : GlobalTheory.NormCurve.finite_integralClosure
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:19.274967+00:00
-- url     : https://prove2.me/theorems/de4fd13f-13ed-5ae9-bbdd-8181de4d882d
-- title:
--   Norm Curve: finite integral Closure
-- statement:
--   The Norm Curve construction uses the finite integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsProperCurveThroughPoint.lean#L36-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsProperCurveThroughPoint.lean#L36-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve

theorem GlobalTheory.NormCurve.finite_integralClosure (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by sorry
