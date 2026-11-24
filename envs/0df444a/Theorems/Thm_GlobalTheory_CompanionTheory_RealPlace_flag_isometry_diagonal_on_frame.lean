-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RealPlace_flag_isometry_diagonal_on_frame
-- name    : GlobalTheory.CompanionTheory.RealPlace.flag_isometry_diagonal_on_frame
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:30.813992+00:00
-- url     : https://prove2.me/theorems/cfc8d518-e5bb-4744-a3ef-be58b71592b2
-- title:
--   Real Place: flag isometry diagonal on frame
-- statement:
--   The Real Place construction uses the flag isometry diagonal on frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqDiagonalOfUpperTriangularOfUnitary.lean#L22-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EqDiagonalOfUpperTriangularOfUnitary.lean#L22-L72

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

theorem GlobalTheory.CompanionTheory.RealPlace.flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by sorry
