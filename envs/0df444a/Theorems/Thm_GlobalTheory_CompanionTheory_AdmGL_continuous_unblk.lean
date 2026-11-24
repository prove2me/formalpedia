-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_continuous_unblk
-- name    : GlobalTheory.CompanionTheory.AdmGL.continuous_unblk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:18.021935+00:00
-- url     : https://prove2.me/theorems/d05ae196-7e3d-4f8a-91c7-cfd1fe3f412a
-- title:
--   Adm GL: continuous unblk
-- statement:
--   The Adm GL construction uses the continuous unblk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L94-L100

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

theorem GlobalTheory.CompanionTheory.AdmGL.continuous_unblk (e : Fin a × ι ≃ Fin n) : Continuous (unblk e) := by sorry
