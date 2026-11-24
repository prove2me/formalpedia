-- Prove2me | Theorems.Thm_GlobalTheory_NoCommonZeroSpread_exists_common_denominator
-- name    : GlobalTheory.NoCommonZeroSpread.exists_common_denominator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:41.459808+00:00
-- url     : https://prove2.me/theorems/393c5aaf-2aae-479f-8319-3510d2f82cdc
-- title:
--   No Common Zero Spread: exists common denominator
-- statement:
--   The No Common Zero Spread construction uses the exists common denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoCommonZeroSpreadsConstructibleNbhd.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoCommonZeroSpreadsConstructibleNbhd.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.NoCommonZeroSpread

theorem GlobalTheory.NoCommonZeroSpread.exists_common_denominator {A Ω : Type} [CommRing A] [Field Ω] (φ : A →+* Ω)
    (S : Finset Ω) (hS : ∀ x ∈ S, x ∈ Subfield.closure (φ.range : Set Ω)) :
    ∃ b : A, φ b ≠ 0 ∧ ∀ x ∈ S, φ b * x ∈ Set.range φ := by sorry
