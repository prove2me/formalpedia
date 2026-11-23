-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inl
-- name    : GlobalTheory.CompanionTheory.IwahoriUDL.ex_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:24.223797+00:00
-- url     : https://prove2.me/theorems/0a5a834a-487f-440b-acdc-67776609fb67
-- title:
--   Iwahori UDL: ex inl
-- statement:
--   The Iwahori UDL construction uses the ex inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean#L11-L11

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

theorem GlobalTheory.CompanionTheory.IwahoriUDL.ex_inl {n : ℕ} (i : Fin n) : ex n (Sum.inl i) = i.castSucc := by sorry
