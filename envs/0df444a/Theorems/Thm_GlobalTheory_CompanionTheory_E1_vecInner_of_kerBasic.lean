-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_E1_vecInner_of_kerBasic
-- name    : GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:02.720016+00:00
-- url     : https://prove2.me/theorems/d7f5a59c-26f0-468c-b439-aa2b3dc252e3
-- title:
--   E1: vec Inner of ker Basic
-- statement:
--   The E1 construction uses the vec Inner of ker Basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecInnerOfKerBasic.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecInnerOfKerBasic.lean#L10-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecInnerOfKerBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.E1

theorem GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic : KerBasic → VecInner := by sorry
