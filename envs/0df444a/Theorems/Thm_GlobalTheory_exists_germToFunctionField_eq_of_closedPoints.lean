-- Prove2me | Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_closedPoints
-- name    : GlobalTheory.exists_germToFunctionField_eq_of_closedPoints
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:46.358015+00:00
-- url     : https://prove2.me/theorems/59523bc9-ac81-4414-81b4-b4bd2a52de7d
-- title:
--   Global Theory: exists germ To Function Field eq of closed Points
-- statement:
--   The Global Theory construction uses the exists germ To Function Field eq of closed Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L295-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L295-L305

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

theorem GlobalTheory.exists_germToFunctionField_eq_of_closedPoints {Z : Scheme.{0}} [IsIntegral Z]
    [JacobsonSpace Z] (W : Z.Opens) [Nonempty W] (t : Z.functionField)
    (h : ∀ x ∈ W, IsClosed ({x} : Set Z) →
      t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) :
    ∃ s : Γ(Z, W), Z.germToFunctionField W s = t := by sorry
