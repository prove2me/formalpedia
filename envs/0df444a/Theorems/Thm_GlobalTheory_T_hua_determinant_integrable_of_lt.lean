-- Prove2me | Theorems.Thm_GlobalTheory_T_hua_determinant_integrable_of_lt
-- name    : GlobalTheory.T.hua_determinant_integrable_of_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:02.637807+00:00
-- url     : https://prove2.me/theorems/d327b77c-4294-4292-b037-384a0386e5f9
-- title:
--   T: hua determinant integrable of lt
-- statement:
--   The T construction uses the hua determinant integrable of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HuaDeterminantIntegrableOfLtStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HuaDeterminantIntegrableOfLtStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by sorry
