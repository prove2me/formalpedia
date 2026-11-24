-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerLinear_kerLin_of_kerBasic
-- name    : GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:36.749708+00:00
-- url     : https://prove2.me/theorems/934d8243-e291-4558-9f9f-7db1fb21b387
-- title:
--   Ker Linear: ker Lin of ker Basic
-- statement:
--   The Ker Linear construction uses the ker Lin of ker Basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerLinOfKerBasic.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerLinOfKerBasic.lean#L8-L36

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerLinOfKerBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerLinear

theorem GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic : KerBasic → KerLin := by sorry
