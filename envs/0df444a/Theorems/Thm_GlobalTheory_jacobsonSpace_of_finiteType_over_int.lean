-- Prove2me | Theorems.Thm_GlobalTheory_jacobsonSpace_of_finiteType_over_int
-- name    : GlobalTheory.jacobsonSpace_of_finiteType_over_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:24.773805+00:00
-- url     : https://prove2.me/theorems/058e5e53-87ad-5032-aa04-152775a9e654
-- title:
--   Global Theory: jacobson Space of finite Type over int
-- statement:
--   The Global Theory construction uses the jacobson Space of finite Type over int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L307-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L307-L311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y

theorem GlobalTheory.jacobsonSpace_of_finiteType_over_int {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ))
    [LocallyOfFiniteType π] : JacobsonSpace Z := by sorry
