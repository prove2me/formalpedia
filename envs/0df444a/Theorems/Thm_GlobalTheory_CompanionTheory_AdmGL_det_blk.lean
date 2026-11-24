-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_det_blk
-- name    : GlobalTheory.CompanionTheory.AdmGL.det_blk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:32.266463+00:00
-- url     : https://prove2.me/theorems/831e2ca7-0f3e-4827-b2c9-98378f8675b5
-- title:
--   Adm GL: det blk
-- statement:
--   The Adm GL construction uses the det blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L105-L107

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

theorem GlobalTheory.CompanionTheory.AdmGL.det_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    (blk e M).det = ∏ w, (atPlace M w).det := by sorry
