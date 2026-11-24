-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixComm_commute_of_dominated_diag
-- name    : GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:09.308485+00:00
-- url     : https://prove2.me/theorems/4881247e-d560-42aa-81c4-a9eab5777049
-- title:
--   Matrix Comm: commute of dominated diag
-- statement:
--   The Matrix Comm construction uses the commute of dominated diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutes.lean#L21-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutes.lean#L21-L49

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

theorem GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hH : (Uᴴ * H * U).IsDiag) (hA : (Uᴴ * A * U).IsDiag)
    (hdom : ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j)
    (hHY : H * Y = Y * H) : Y * A = A * Y := by sorry
