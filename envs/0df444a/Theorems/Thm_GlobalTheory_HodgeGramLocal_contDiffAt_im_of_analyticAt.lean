-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_contDiffAt_im_of_analyticAt
-- name    : GlobalTheory.HodgeGramLocal.contDiffAt_im_of_analyticAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:30.602877+00:00
-- url     : https://prove2.me/theorems/db28825f-5373-4083-9ee0-651d39458af5
-- title:
--   Hodge Gram Local: cont Diff At im of analytic At
-- statement:
--   The Hodge Gram Local construction uses the cont Diff At im of analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L35-L37

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

theorem GlobalTheory.HodgeGramLocal.contDiffAt_im_of_analyticAt {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z := by sorry
