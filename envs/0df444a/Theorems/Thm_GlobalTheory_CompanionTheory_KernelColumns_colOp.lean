-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_colOp
-- name    : GlobalTheory.CompanionTheory.KernelColumns.colOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:55.962158+00:00
-- url     : https://prove2.me/theorems/1e4eccb5-905c-4c0a-82a4-ede35c81f742
-- title:
--   Kernel Columns: col Op
-- statement:
--   The Kernel Columns construction uses the col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ColOp.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ColOp.lean#L11-L60

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns

theorem GlobalTheory.CompanionTheory.KernelColumns.colOp : KerBasic → CvTest → KernelL2RowsColumns → KerMul → ColOp := by sorry
