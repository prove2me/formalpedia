-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_injective
-- name    : GlobalTheory.CompanionTheory.AdmGL.blk_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:58:43.716717+00:00
-- url     : https://prove2.me/theorems/ee2716df-8465-4773-b5bd-c95cf3d08eeb
-- title:
--   Adm GL: blk injective
-- statement:
--   The Adm GL construction uses the blk injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L33-L35

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

theorem GlobalTheory.CompanionTheory.AdmGL.blk_injective (e : Fin a × ι ≃ Fin n) : Function.Injective (blk e) := by sorry
