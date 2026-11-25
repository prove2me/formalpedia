-- Prove2me | Theorems.Thm_GlobalTheory_NormCurve_exists_point
-- name    : GlobalTheory.NormCurve.exists_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:18.454151+00:00
-- url     : https://prove2.me/theorems/075f982d-b2ef-5d38-ae3b-4f37d584015c
-- title:
--   Norm Curve: exists point
-- statement:
--   The Norm Curve construction uses the exists point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsProperCurveThroughPoint.lean#L216-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsProperCurveThroughPoint.lean#L216-L271

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

theorem GlobalTheory.NormCurve.exists_point {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ Sp k) [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) (W : X.Opens)
    (hW : Nonempty W) : ∃ ξ : X, ξ ∈ W ∧ ξ ⤳ x ∧
      letI := (constHom (X.fromSpecResidueField ξ ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (X.residueField ξ), ⊤) ≤ 1 := by sorry
