-- Prove2me | Theorems.Thm_GlobalTheory_TangentCriterion_unramified_quasiFinite_of_tangent
-- name    : GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:21.052262+00:00
-- url     : https://prove2.me/theorems/87bdb163-acc1-4487-92b8-7dc5b322655d
-- title:
--   Tangent Criterion: unramified quasi Finite of tangent
-- statement:
--   The Tangent Criterion construction uses the unramified quasi Finite of tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnramifiedQuasiFiniteOfTangent.lean#L59-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnramifiedQuasiFiniteOfTangent.lean#L59-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.TangentCriterion

theorem GlobalTheory.TangentCriterion.unramified_quasiFinite_of_tangent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f → (∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ X), x ≫ f = constPt x ≫ f → x = constPt x) → FormallyUnramified f ∧ LocallyQuasiFinite f := by sorry
