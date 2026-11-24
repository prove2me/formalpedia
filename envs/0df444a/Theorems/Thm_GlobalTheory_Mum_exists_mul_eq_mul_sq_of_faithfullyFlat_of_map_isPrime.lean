-- Prove2me | Theorems.Thm_GlobalTheory_Mum_exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime
-- name    : GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:26.377194+00:00
-- url     : https://prove2.me/theorems/ab39b8ba-a6aa-4019-a762-c4b6fe6aab54
-- title:
--   Mum: exists mul eq mul sq of faithfully Flat of map is Prime
-- statement:
--   The Mum construction uses the exists mul eq mul sq of faithfully Flat of map is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOne.lean#L49-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOne.lean#L49-L107

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

theorem GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by sorry
