-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_ddbar_im_of_contDiffAt
-- name    : GlobalTheory.HodgeGramLocal.ddbar_im_of_contDiffAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:21.992838+00:00
-- url     : https://prove2.me/theorems/ece3b0d2-baa2-4c24-8896-99639451f4ce
-- title:
--   Hodge Gram Local: ddbar im of cont Diff At
-- statement:
--   The Hodge Gram Local construction uses the ddbar im of cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L28-L33

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem GlobalTheory.HodgeGramLocal.ddbar_im_of_contDiffAt {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by sorry
