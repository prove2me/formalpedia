-- Prove2me | Theorems.Thm_GlobalTheory_TangentCriterion_formallyUnramified_of_tangent
-- name    : GlobalTheory.TangentCriterion.formallyUnramified_of_tangent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:14.325625+00:00
-- url     : https://prove2.me/theorems/86c2f82b-c976-40de-80ef-6821063f9b65
-- title:
--   Tangent Criterion: formally Unramified of tangent
-- statement:
--   The Tangent Criterion construction uses the formally Unramified of tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnramifiedQuasiFiniteOfTangent.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UnramifiedQuasiFiniteOfTangent.lean#L28-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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

theorem GlobalTheory.TangentCriterion.formallyUnramified_of_tangent {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (h : ∀ (K : Type) [Field K] (g : B →+* DualNumber K),
      g.comp (algebraMap A B) = (((algebraMap K (DualNumber K)).comp
        (TrivSqZeroExt.fstHom K K K).toRingHom).comp g).comp (algebraMap A B) →
      g = ((algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom).comp g) :
    Algebra.FormallyUnramified A B := by sorry
