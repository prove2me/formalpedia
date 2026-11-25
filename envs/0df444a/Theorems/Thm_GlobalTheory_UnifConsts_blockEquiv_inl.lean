-- Prove2me | Theorems.Thm_GlobalTheory_UnifConsts_blockEquiv_inl
-- name    : GlobalTheory.UnifConsts.blockEquiv_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:10.282454+00:00
-- url     : https://prove2.me/theorems/d90a3000-84b8-4122-a34a-473b310c85f9
-- title:
--   Unif Consts: block Equiv inl
-- statement:
--   The Unif Consts construction uses the block Equiv inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L111-L112

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

theorem GlobalTheory.UnifConsts.blockEquiv_inl (g rk : ℕ) (i) : (blockEquiv g rk (Sum.inl i)).val < rk := by sorry
