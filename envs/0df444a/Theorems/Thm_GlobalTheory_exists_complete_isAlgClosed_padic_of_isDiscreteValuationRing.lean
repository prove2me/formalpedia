-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing
-- name    : GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:27.506109+00:00
-- url     : https://prove2.me/theorems/cd8ecdba-bf71-450f-af9c-c3e6f05eaa63
-- title:
--   Global Theory: exists complete is Alg Closed padic of is Discrete Valuation Ring
-- statement:
--   The Global Theory construction uses the exists complete is Alg Closed padic of is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L448-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L448-L473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (hV : (p : V) ∈ IsLocalRing.maximalIdeal V) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
      ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range := by sorry
