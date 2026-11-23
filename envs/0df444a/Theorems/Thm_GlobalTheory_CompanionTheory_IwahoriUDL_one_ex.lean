-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_one_ex
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.one_ex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:50.348574+00:00
-- url     : https://prove2.me/theorems/f1411056-9695-47ae-b985-79272045cafc
-- title:
--   Iwahori UDL: one ex
-- statement:
--   The Iwahori UDL construction uses the one ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L19-L23

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

theorem GlobalTheory.CompanionTheory.IwahoriUDL.one_ex {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ex n i) (ex n j) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) i j := by sorry
