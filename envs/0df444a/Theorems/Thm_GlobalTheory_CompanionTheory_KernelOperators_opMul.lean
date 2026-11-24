-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelOperators_opMul
-- name    : GlobalTheory.CompanionTheory.KernelOperators.opMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:05.983993+00:00
-- url     : https://prove2.me/theorems/cc1b9725-7c40-404e-adac-6b977e590384
-- title:
--   Kernel Operators: op Mul
-- statement:
--   The Kernel Operators construction uses the op Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompKey.lean#L37-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompKey.lean#L37-L72

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompKey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelOperators

theorem GlobalTheory.CompanionTheory.KernelOperators.opMul : KerBasic → KerLin → RowInt → KernelL2RowsColumns → SchurInt → CvTest → KerMul → OpMul := by sorry
