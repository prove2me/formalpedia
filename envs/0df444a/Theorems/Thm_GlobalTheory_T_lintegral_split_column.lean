-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_split_column
-- name    : GlobalTheory.T.lintegral_split_column
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:52:14.300044+00:00
-- url     : https://prove2.me/theorems/3b6a1479-15af-4552-a7dc-5cda78c132c8
-- title:
--   T: lintegral split column
-- statement:
--   The T construction uses the lintegral split column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumnStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralSplitColumnStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumn
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lintegral_split_column : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by sorry
