-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QR_exists_unitary_mul_blockTriangular
-- name    : GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:31:51.932096+00:00
-- url     : https://prove2.me/theorems/9a7dfa3f-3cc5-4dd0-a9a7-9da2c8724c28
-- title:
--   QR: exists unitary mul block Triangular
-- statement:
--   The QR construction uses the exists unitary mul block Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwasawaUnitaryUpperTriangular.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwasawaUnitaryUpperTriangular.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwasawaUnitaryUpperTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QR

theorem GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by sorry
