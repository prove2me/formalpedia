-- Prove2me | Theorems.Thm_GlobalTheory_Mum_exists_uniformiser_mul_eq_mul_pow_of_height_eq_one
-- name    : GlobalTheory.Mum.exists_uniformiser_mul_eq_mul_pow_of_height_eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:22.825392+00:00
-- url     : https://prove2.me/theorems/cea5f36a-d8d6-43e4-8e47-c89b98a54147
-- title:
--   Mum: exists uniformiser mul eq mul pow of height eq one
-- statement:
--   The Mum construction uses the exists uniformiser mul eq mul pow of height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOne.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOne.lean#L7-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_uniformiser_mul_eq_mul_pow_of_height_eq_one (O : Type) [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [IsIntegrallyClosed O] (p : Ideal O) [hp : p.IsPrime] (h1 : p.height = 1)
    (h : O) (hh : h ≠ 0) :
    ∃ π ∈ p, π ≠ 0 ∧ (∀ y ∈ p, ∃ s ∉ p, π ∣ s * y) ∧
      ∃ (n : ℕ) (b c : O), b ∉ p ∧ c ∉ p ∧ b * h = c * π ^ n := by sorry
