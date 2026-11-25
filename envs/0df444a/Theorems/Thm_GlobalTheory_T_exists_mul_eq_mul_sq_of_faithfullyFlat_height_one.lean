-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_mul_eq_mul_sq_of_faithfullyFlat_height_one
-- name    : GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:49.427561+00:00
-- url     : https://prove2.me/theorems/bbbc5ae2-bdb5-5fa0-8c24-cdc05a3c0b4f
-- title:
--   T: exists mul eq mul sq of faithfully Flat height one
-- statement:
--   The T construction uses the exists mul eq mul sq of faithfully Flat height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by sorry
