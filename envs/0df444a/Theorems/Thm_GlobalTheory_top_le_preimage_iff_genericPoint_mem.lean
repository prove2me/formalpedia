-- Prove2me | Theorems.Thm_GlobalTheory_top_le_preimage_iff_genericPoint_mem
-- name    : GlobalTheory.top_le_preimage_iff_genericPoint_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:15:35.75106+00:00
-- url     : https://prove2.me/theorems/3b7f526c-e551-58d6-bc42-e98641bf32ab
-- title:
--   Global Theory: top le preimage iff generic Point mem
-- statement:
--   The Global Theory construction uses the top le preimage iff generic Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L266-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L266-L279

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

theorem GlobalTheory.top_le_preimage_iff_genericPoint_mem {O K : Type} [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [FaithfulSMul O K] {Z : Scheme.{0}} (y : Spec (.of O) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ y) ⁻¹ᵁ U ↔ y (genericPoint _) ∈ U := by sorry
