-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_det_apply_place
-- name    : GlobalTheory.CompanionTheory.AdmGL.det_apply_place
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:16.710625+00:00
-- url     : https://prove2.me/theorems/fd29bf12-91f1-45bc-862e-6e34c5bbf93f
-- title:
--   Adm GL: det apply place
-- statement:
--   The Adm GL construction uses the det apply place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L102-L103

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

theorem GlobalTheory.CompanionTheory.AdmGL.det_apply_place (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : M.det w = (atPlace M w).det := by sorry
