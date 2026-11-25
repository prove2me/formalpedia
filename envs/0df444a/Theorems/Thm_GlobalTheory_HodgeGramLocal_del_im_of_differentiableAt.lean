-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_del_im_of_differentiableAt
-- name    : GlobalTheory.HodgeGramLocal.del_im_of_differentiableAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:37.660745+00:00
-- url     : https://prove2.me/theorems/b6506a4b-dad3-4658-a705-9d72780f8401
-- title:
--   Hodge Gram Local: del im of differentiable At
-- statement:
--   The Hodge Gram Local construction uses the del im of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L17-L26

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

theorem GlobalTheory.HodgeGramLocal.del_im_of_differentiableAt {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by sorry
