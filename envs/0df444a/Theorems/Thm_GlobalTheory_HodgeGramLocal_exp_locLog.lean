-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_exp_locLog
-- name    : GlobalTheory.HodgeGramLocal.exp_locLog
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:54.17473+00:00
-- url     : https://prove2.me/theorems/cb2cdb8a-2c3b-4c5a-8040-1c5762b2ae5b
-- title:
--   Hodge Gram Local: exp loc Log
-- statement:
--   The Hodge Gram Local construction uses the exp loc Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L43-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal

theorem GlobalTheory.HodgeGramLocal.exp_locLog {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by sorry
