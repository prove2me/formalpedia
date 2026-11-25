-- Prove2me | Theorems.Thm_GlobalTheory_UnifConsts_quad_abs_le
-- name    : GlobalTheory.UnifConsts.quad_abs_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:33.201936+00:00
-- url     : https://prove2.me/theorems/fbfb88b8-bf9b-4c2a-adde-071cdf177968
-- title:
--   Unif Consts: quad abs le
-- statement:
--   The Unif Consts construction uses the quad abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L10-L35

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

theorem GlobalTheory.UnifConsts.quad_abs_le {m : Type} [Fintype m] (A : Matrix m m ℝ) (E : ℝ)
    (hE : ∀ j k, |A j k| ≤ E) (x : m → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ E * Fintype.card m * (x ⬝ᵥ x) := by sorry
