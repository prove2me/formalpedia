-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_hasDerivAt_locLog
-- name    : GlobalTheory.HodgeGramLocal.hasDerivAt_locLog
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:20.713594+00:00
-- url     : https://prove2.me/theorems/4831a5c6-1dbd-4264-8a39-97a6b6e6ae6f
-- title:
--   Hodge Gram Local: has Deriv At loc Log
-- statement:
--   The Hodge Gram Local construction uses the has Deriv At loc Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L47-L49

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

theorem GlobalTheory.HodgeGramLocal.hasDerivAt_locLog {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w := by sorry
