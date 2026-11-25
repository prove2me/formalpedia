-- Prove2me | Theorems.Thm_GlobalTheory_T_contDiff_tsum_of_summable_iteratedFDeriv_bounds
-- name    : GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:45.954634+00:00
-- url     : https://prove2.me/theorems/a5832802-c2ca-468c-818b-5985813679b0
-- title:
--   T: cont Diff tsum of summable iterated FDeriv bounds
-- statement:
--   The T construction uses the cont Diff tsum of summable iterated FDeriv bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffTsumOfLocallySummableBoundsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffTsumOfLocallySummableBoundsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffTsumOfLocallySummableBounds
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffTsumOfLocallySummableBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by sorry
