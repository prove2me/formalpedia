-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixComm_commute_diagonal_of_dominated
-- name    : GlobalTheory.CompanionTheory.MatrixComm.commute_diagonal_of_dominated
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:01.75688+00:00
-- url     : https://prove2.me/theorems/6e23f2ab-e78a-49dd-b6c3-f0b167101e57
-- title:
--   Matrix Comm: commute diagonal of dominated
-- statement:
--   The Matrix Comm construction uses the commute diagonal of dominated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutes.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutes.lean#L6-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixComm

theorem GlobalTheory.CompanionTheory.MatrixComm.commute_diagonal_of_dominated {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by sorry
