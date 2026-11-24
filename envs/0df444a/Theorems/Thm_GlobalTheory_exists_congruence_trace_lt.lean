-- Prove2me | Theorems.Thm_GlobalTheory_exists_congruence_trace_lt
-- name    : GlobalTheory.exists_congruence_trace_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:10.037339+00:00
-- url     : https://prove2.me/theorems/5e68bdf3-faca-4956-9155-f6406a1ec09d
-- title:
--   Global Theory: exists congruence trace lt
-- statement:
--   The Global Theory construction uses the exists congruence trace lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L60-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L60-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
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

theorem GlobalTheory.exists_congruence_trace_lt :
    ∀ (g N : ℕ), 2 ≤ g → 1 ≤ N → ∀ T : Matrix (Fin g) (Fin g) ℚ, T.IsSymm →
      (∃ v : Fin g → ℚ, v ⬝ᵥ T.mulVec v < 0) →
      ∀ c : ℚ, ∃ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 ∧
        (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) ∧
        ((U.map (Int.cast : ℤ → ℚ)).transpose * T * U.map (Int.cast : ℤ → ℚ)).trace < c := by sorry
