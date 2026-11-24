-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_forall_complexPoint_extend
-- name    : GlobalTheory.exists_ne_zero_forall_complexPoint_extend
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:18.347978+00:00
-- url     : https://prove2.me/theorems/e568ca71-d4f5-4f47-91ec-acee2e09be56
-- title:
--   Global Theory: exists ne zero forall complex Point extend
-- statement:
--   The Global Theory construction uses the exists ne zero forall complex Point extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtend.lean#L64-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroForallComplexPointExtend.lean#L64-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroForallComplexPointExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_ne_zero_forall_complexPoint_extend :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by sorry
