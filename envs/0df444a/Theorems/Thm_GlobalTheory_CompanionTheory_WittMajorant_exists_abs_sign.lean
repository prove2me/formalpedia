-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WittMajorant_exists_abs_sign
-- name    : GlobalTheory.CompanionTheory.WittMajorant.exists_abs_sign
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:56.881991+00:00
-- url     : https://prove2.me/theorems/9626f6a5-3fd0-4a1d-88ed-b4ef4409f6b3
-- title:
--   Witt Majorant: exists abs sign
-- statement:
--   The Witt Majorant construction uses the exists abs sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsAdaptedMajorant.lean#L17-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsAdaptedMajorant.lean#L17-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsAdaptedMajorant
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittMajorant
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.WittMajorant.exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by sorry
