-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_diagonal_commutator
-- name    : GlobalTheory.CompanionTheory.AdProj.diagonal_commutator
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:16.02949+00:00
-- url     : https://prove2.me/theorems/24d6fd92-9193-46f0-9864-9af317da0eee
-- title:
--   Ad Proj: diagonal commutator
-- statement:
--   The Ad Proj construction uses the diagonal commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraFunctionCalculus.lean#L10-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdProj

theorem GlobalTheory.CompanionTheory.AdProj.diagonal_commutator {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by sorry
