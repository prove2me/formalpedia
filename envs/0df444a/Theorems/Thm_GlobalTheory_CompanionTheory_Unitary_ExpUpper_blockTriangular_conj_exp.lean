-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_ExpUpper_blockTriangular_conj_exp
-- name    : GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:35.094627+00:00
-- url     : https://prove2.me/theorems/1ceb54cf-b7ae-4287-95ee-c511afcc18ca
-- title:
--   Exp Upper: block Triangular conj exp
-- statement:
--   The Exp Upper construction uses the block Triangular conj exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExpBlockTriangular.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExpBlockTriangular.lean#L17-L25

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

theorem GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by sorry
