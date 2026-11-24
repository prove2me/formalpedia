-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RealPlace_eq_diagonal_of_upperTriangular_of_unitary
-- name    : GlobalTheory.CompanionTheory.RealPlace.eq_diagonal_of_upperTriangular_of_unitary
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:20.209371+00:00
-- url     : https://prove2.me/theorems/2333a9c9-29a4-4d37-b633-99584204882b
-- title:
--   Real Place: eq diagonal of upper Triangular of unitary
-- statement:
--   The Real Place construction uses the eq diagonal of upper Triangular of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqDiagonalOfUpperTriangularOfUnitary.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqDiagonalOfUpperTriangularOfUnitary.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqDiagonalOfUpperTriangularOfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RealPlace

theorem GlobalTheory.CompanionTheory.RealPlace.eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by sorry
