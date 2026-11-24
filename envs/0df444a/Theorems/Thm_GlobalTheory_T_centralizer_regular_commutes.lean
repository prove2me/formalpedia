-- Prove2me | Theorems.Thm_GlobalTheory_T_centralizer_regular_commutes
-- name    : GlobalTheory.T.centralizer_regular_commutes
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:30:51.251205+00:00
-- url     : https://prove2.me/theorems/8be189ef-84b7-4bc8-a359-afcce717763e
-- title:
--   T: centralizer regular commutes
-- statement:
--   The T construction uses the centralizer regular commutes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralizerRegularCommutesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutes
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.centralizer_regular_commutes : ∀ {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * H * U).IsDiag → (Uᴴ * A * U).IsDiag → (∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j) → H * Y = Y * H → Y * A = A * Y := by sorry
