-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RowSect_exists_GL_last_row
-- name    : GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:04.232001+00:00
-- url     : https://prove2.me/theorems/69050c27-d0d3-4fb1-b9e0-b1da4980984a
-- title:
--   Row Sect: exists GL last row
-- statement:
--   The Row Sect construction uses the exists GL last row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLLastBasisVecMulEq.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLLastBasisVecMulEq.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLLastBasisVecMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RowSect

theorem GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k) (hξ : ξ ≠ 0) :
    ∃ h : GL (Fin (m + 1)) k,
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by sorry
