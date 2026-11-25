-- Prove2me | Theorems.Thm_GlobalTheory_finiteType_int_of_finiteType
-- name    : GlobalTheory.finiteType_int_of_finiteType
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:22.430939+00:00
-- url     : https://prove2.me/theorems/b17d37ac-c6ec-44d5-8d42-b9bce0c31a77
-- title:
--   Global Theory: finite Type int of finite Type
-- statement:
--   The Global Theory construction uses the finite Type int of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L12-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.finiteType_int_of_finiteType (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType A B] : Algebra.FiniteType ℤ B := by sorry
