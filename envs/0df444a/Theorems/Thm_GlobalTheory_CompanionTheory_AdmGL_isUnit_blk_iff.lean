-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_isUnit_blk_iff
-- name    : GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:07.847103+00:00
-- url     : https://prove2.me/theorems/a259afc7-721c-4289-9cb8-06226e1388ae
-- title:
--   Adm GL: is Unit blk iff
-- statement:
--   The Adm GL construction uses the is Unit blk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L109-L112

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

theorem GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    IsUnit (blk e M) ↔ IsUnit M := by sorry
