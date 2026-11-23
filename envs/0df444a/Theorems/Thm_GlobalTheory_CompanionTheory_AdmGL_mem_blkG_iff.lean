-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_mem_blkG_iff
-- name    : GlobalTheory.CompanionTheory.AdmGL.mem_blkG_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:59.684843+00:00
-- url     : https://prove2.me/theorems/08fe3491-7e03-4a25-b5d7-17d08d49bf10
-- title:
--   Adm GL: mem blk G iff
-- statement:
--   The Adm GL construction uses the mem blk G iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L114-L122

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

theorem GlobalTheory.CompanionTheory.AdmGL.mem_blkG_iff (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ blkG e ↔ IsUnit g ∧ blk e (unblk e g) = g := by sorry
