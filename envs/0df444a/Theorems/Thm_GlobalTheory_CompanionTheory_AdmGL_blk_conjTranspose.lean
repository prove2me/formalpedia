-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_conjTranspose
-- name    : GlobalTheory.CompanionTheory.AdmGL.blk_conjTranspose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:52.774805+00:00
-- url     : https://prove2.me/theorems/90c8a73a-d3db-43f3-988e-ecc67ce0c982
-- title:
--   Adm GL: blk conj Transpose
-- statement:
--   The Adm GL construction uses the blk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L76-L82

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

theorem GlobalTheory.CompanionTheory.AdmGL.blk_conjTranspose (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e Mᴴ = (blk e M)ᴴ := by sorry
