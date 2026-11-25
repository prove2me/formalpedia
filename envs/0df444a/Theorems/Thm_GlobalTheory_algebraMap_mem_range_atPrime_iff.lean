-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_mem_range_atPrime_iff
-- name    : GlobalTheory.algebraMap_mem_range_atPrime_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:20.568078+00:00
-- url     : https://prove2.me/theorems/ae43d7e4-43ed-5a69-925a-6edb6af81f6b
-- title:
--   Global Theory: algebra Map mem range at Prime iff
-- statement:
--   The Global Theory construction uses the algebra Map mem range at Prime iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L163-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L163-L190

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
variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]
variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]
omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] [IsLocalization.Away a S]

theorem GlobalTheory.algebraMap_mem_range_atPrime_iff (a : A) [IsLocalization.Away a S] (m : Ideal A) [m.IsPrime]
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m]
    (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F] [Algebra L F]
    [IsScalarTower A S F] [IsScalarTower A L F] (φ : S) :
    algebraMap S F φ ∈ (algebraMap L F).range ↔
      ∃ s ∉ m, ∃ b : A, algebraMap A S s * φ = algebraMap A S b := by sorry
