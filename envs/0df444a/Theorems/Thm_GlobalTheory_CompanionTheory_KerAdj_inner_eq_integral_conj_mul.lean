-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerAdj_inner_eq_integral_conj_mul
-- name    : GlobalTheory.CompanionTheory.KerAdj.inner_eq_integral_conj_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:21.941887+00:00
-- url     : https://prove2.me/theorems/74a4bec7-3e2b-4eaa-8fde-bb1f4663f6d2
-- title:
--   Ker Adj: inner eq integral conj mul
-- statement:
--   The Ker Adj construction uses the inner eq integral conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerEqIntegralConjMul.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerEqIntegralConjMul.lean#L39-L43

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

theorem GlobalTheory.CompanionTheory.KerAdj.inner_eq_integral_conj_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} (u v : Lp ℂ 2 ν) :
    inner ℂ u v = ∫ x, conj ((u : α → ℂ) x) * (v : α → ℂ) x ∂ν := by sorry
