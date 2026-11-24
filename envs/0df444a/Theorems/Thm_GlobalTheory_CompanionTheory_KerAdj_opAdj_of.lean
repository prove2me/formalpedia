-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerAdj_opAdj_of
-- name    : GlobalTheory.CompanionTheory.KerAdj.opAdj_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:32.57203+00:00
-- url     : https://prove2.me/theorems/a00b09d8-2c4d-416f-882f-a4d3f114ce95
-- title:
--   Ker Adj: op Adj of
-- statement:
--   The Ker Adj construction uses the op Adj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerEqIntegralConjMul.lean#L59-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerEqIntegralConjMul.lean#L59-L88

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerEqIntegralConjMul
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
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerAdj

theorem GlobalTheory.CompanionTheory.KerAdj.opAdj_of : KerBasic → RowInt → SchurInt → OpExA → OpAdj := by sorry
