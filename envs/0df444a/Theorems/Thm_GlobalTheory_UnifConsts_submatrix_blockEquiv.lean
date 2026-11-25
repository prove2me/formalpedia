-- Prove2me | Theorems.Thm_GlobalTheory_UnifConsts_submatrix_blockEquiv
-- name    : GlobalTheory.UnifConsts.submatrix_blockEquiv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:59.971388+00:00
-- url     : https://prove2.me/theorems/161fa58d-be38-4be9-8fcb-f0631f869e97
-- title:
--   Unif Consts: submatrix block Equiv
-- statement:
--   The Unif Consts construction uses the submatrix block Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L117-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L117-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts

theorem GlobalTheory.UnifConsts.submatrix_blockEquiv {g rk : ℕ} (Y S : Matrix (Fin g) (Fin g) ℝ) (T : ℝ)
    (hY : ∀ j k, Y j k = Y k j) (hS : ∀ j k, (rk ≤ j.val ∨ rk ≤ k.val) → S j k = 0) :
    (Y + T • S).submatrix (blockEquiv g rk) (blockEquiv g rk) =
      fromBlocks
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl) +
          T • S.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inl))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))
        (Y.submatrix (blockEquiv g rk ∘ Sum.inl) (blockEquiv g rk ∘ Sum.inr))ᵀ
        (Y.submatrix (blockEquiv g rk ∘ Sum.inr) (blockEquiv g rk ∘ Sum.inr)) := by sorry
