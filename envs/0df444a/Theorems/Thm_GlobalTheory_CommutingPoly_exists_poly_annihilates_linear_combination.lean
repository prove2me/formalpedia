-- Prove2me | Theorems.Thm_GlobalTheory_CommutingPoly_exists_poly_annihilates_linear_combination
-- name    : GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:16:48.425002+00:00
-- url     : https://prove2.me/theorems/8716f7bd-9a18-4e84-a93c-5c91d9f5238b
-- title:
--   Commuting Poly: exists poly annihilates linear combination
-- statement:
--   The Commuting Poly construction uses the exists poly annihilates linear combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyAnnihilatesCommutingLinearCombination.lean#L9-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolyAnnihilatesCommutingLinearCombination.lean#L9-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyAnnihilatesCommutingLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CommutingPoly

theorem GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by sorry
