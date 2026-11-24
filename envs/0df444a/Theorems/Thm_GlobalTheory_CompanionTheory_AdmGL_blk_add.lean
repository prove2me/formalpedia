-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_add
-- name    : GlobalTheory.CompanionTheory.AdmGL.blk_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:31.239252+00:00
-- url     : https://prove2.me/theorems/b6f81f0a-48f6-427d-8caf-3bf95dd6e408
-- title:
--   Adm GL: blk add
-- statement:
--   The Adm GL construction uses the blk add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L63-L68

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

theorem GlobalTheory.CompanionTheory.AdmGL.blk_add (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M + N) = blk e M + blk e N := by sorry
