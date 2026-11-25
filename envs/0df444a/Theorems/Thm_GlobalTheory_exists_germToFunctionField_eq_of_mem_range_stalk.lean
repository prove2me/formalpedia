-- Prove2me | Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_mem_range_stalk
-- name    : GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:26.530817+00:00
-- url     : https://prove2.me/theorems/3f5982af-350f-4957-a81b-989b567caad8
-- title:
--   Global Theory: exists germ To Function Field eq of mem range stalk
-- statement:
--   The Global Theory construction uses the exists germ To Function Field eq of mem range stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L281-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L281-L293

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

theorem GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk {Z : Scheme.{0}} [IsIntegral Z]
    {t : Z.functionField} {x : Z}
    (h : t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) {W : Z.Opens} (hx : x ∈ W) :
    ∃ (V : Z.Opens) (_ : Nonempty V) (s : Γ(Z, V)),
      x ∈ V ∧ V ≤ W ∧ Z.germToFunctionField V s = t := by sorry
