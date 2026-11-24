-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_lo_step
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.lo_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:46.924417+00:00
-- url     : https://prove2.me/theorems/8eb71e85-6253-44ff-b337-17ab267788be
-- title:
--   Iwahori UDL: lo step
-- statement:
--   The Iwahori UDL construction uses the lo step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L67-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L67-L96

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]

theorem GlobalTheory.CompanionTheory.IwahoriUDL.lo_step {I : Ideal R} {n : ℕ} {l : Matrix (Fin n) (Fin n) R} (hl : IsLo I l)
    {y : Matrix (Fin 1) (Fin n) R} (hy : ∀ k j, y k j ∈ I) :
    IsLo I ((fromBlocks l 0 y 1).submatrix (ex n).symm (ex n).symm) := by sorry
