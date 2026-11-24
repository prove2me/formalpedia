-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_vecClose_of_kerBasic_colSq
-- name    : GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:20.71108+00:00
-- url     : https://prove2.me/theorems/4c2b8463-f96f-49c0-a271-c8436cf2fd42
-- title:
--   Kernel Columns: vec Close of ker Basic col Sq
-- statement:
--   The Kernel Columns construction uses the vec Close of ker Basic col Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/VecCloseOfKerBasicColSq.lean#L34-L66

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecCloseOfKerBasicColSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns

theorem GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq : KerBasic → ColSq → VecClose := by sorry
