-- Prove2me | Theorems.Thm_GlobalTheory_minkowski_det_bound_posSemidef
-- name    : GlobalTheory.minkowski_det_bound_posSemidef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:23.407915+00:00
-- url     : https://prove2.me/theorems/e1db6ce5-ef5a-4a5f-8579-d5e416affc02
-- title:
--   Global Theory: minkowski det bound pos Semidef
-- statement:
--   The Global Theory construction uses the minkowski det bound pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/MinkowskiDetBoundGramOfDetNeZero.lean#L62-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/MinkowskiDetBoundGramOfDetNeZero.lean#L62-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_MinkowskiDetBoundGramOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.minkowski_det_bound_posSemidef :
    ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → ∀ a : ℝ, 0 ≤ a →
      (∀ z : Fin m → ℤ, z ≠ 0 → a ≤ (fun i => (z i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (z i : ℝ))) →
      a ^ m ≤ (m : ℝ) ^ m * G.det := by sorry
