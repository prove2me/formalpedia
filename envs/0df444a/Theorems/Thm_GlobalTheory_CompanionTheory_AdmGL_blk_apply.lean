-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply
-- name    : GlobalTheory.CompanionTheory.AdmGL.blk_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:23.496053+00:00
-- url     : https://prove2.me/theorems/2d9762cc-60c7-41f8-a1a8-d4c526815a25
-- title:
--   Adm GL: blk apply
-- statement:
--   The Adm GL construction uses the blk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L23-L26

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

theorem GlobalTheory.CompanionTheory.AdmGL.blk_apply (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin n) :
    blk e M i j = if (e.symm i).2 = (e.symm j).2 then M (e.symm i).1 (e.symm j).1 (e.symm i).2 else 0 := by sorry
