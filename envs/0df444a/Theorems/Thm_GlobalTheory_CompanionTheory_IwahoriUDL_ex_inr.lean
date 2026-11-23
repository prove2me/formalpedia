-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inr
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.ex_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:27.569693+00:00
-- url     : https://prove2.me/theorems/3b12b826-d21f-40ad-95d7-e5d8f960b007
-- title:
--   Iwahori UDL: ex inr
-- statement:
--   The Iwahori UDL construction uses the ex inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L13-L17

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

theorem GlobalTheory.CompanionTheory.IwahoriUDL.ex_inr {n : ℕ} (k : Fin 1) : ex n (Sum.inr k) = Fin.last n := by sorry
