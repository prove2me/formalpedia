-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_ExpUpper_blockTriangular_exp
-- name    : GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:51.81604+00:00
-- url     : https://prove2.me/theorems/29a92b41-ae75-478f-b063-27f514b67e38
-- title:
--   Exp Upper: block Triangular exp
-- statement:
--   The Exp Upper construction uses the block Triangular exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExpBlockTriangular.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExpBlockTriangular.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExpBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Unitary GlobalTheory.CompanionTheory.Unitary.ExpUpper
open scoped Matrix.Norms.L2Operator

theorem GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by sorry
