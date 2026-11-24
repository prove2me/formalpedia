-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_di_step
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.di_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:42.608108+00:00
-- url     : https://prove2.me/theorems/d3ac2084-f516-4364-9bd9-3770bec6cd90
-- title:
--   Iwahori UDL: di step
-- statement:
--   The Iwahori UDL construction uses the di step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L98-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L98-L120

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

theorem GlobalTheory.CompanionTheory.IwahoriUDL.di_step {I : Ideal R} {n : ℕ} {d : Matrix (Fin n) (Fin n) R} (hd : IsDi I d)
    {a : Matrix (Fin 1) (Fin 1) R} (ha : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I) :
    IsDi I ((fromBlocks d 0 0 a).submatrix (ex n).symm (ex n).symm) := by sorry
