-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_sliceCLM_add_eq
-- name    : GlobalTheory.SchwartzFstOp.sliceCLM_add_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:48:18.861827+00:00
-- url     : https://prove2.me/theorems/82a8492f-3964-4be3-a3b3-ff8f46767102
-- title:
--   Schwartz Fst Op: slice CLM add eq
-- statement:
--   The Schwartz Fst Op construction uses the slice CLM add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L16-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
noncomputable section
open Filter Topology Asymptotics
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.SchwartzFstOp.sliceCLM_add_eq (x' v : V') (f : 𝓢(V × V', ℂ)) :
    sliceCLM (x' + v) f = sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f) := by sorry
