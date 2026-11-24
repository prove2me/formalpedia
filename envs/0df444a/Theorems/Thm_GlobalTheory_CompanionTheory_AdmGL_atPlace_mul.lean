-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_atPlace_mul
-- name    : GlobalTheory.CompanionTheory.AdmGL.atPlace_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:13.281691+00:00
-- url     : https://prove2.me/theorems/b74e163b-ab22-445a-93d0-9cd814fd333f
-- title:
--   Adm GL: at Place mul
-- statement:
--   The Adm GL construction uses the at Place mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlkConjTranspose.lean#L50-L53

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

theorem GlobalTheory.CompanionTheory.AdmGL.atPlace_mul (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    atPlace (M * N) w = atPlace M w * atPlace N w := by sorry
