-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_opFst_add_decomp
-- name    : GlobalTheory.SchwartzFstOp.opFst_add_decomp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:48:14.20369+00:00
-- url     : https://prove2.me/theorems/a5a3663e-ee4c-453c-aad4-0a98d4c21756
-- title:
--   Schwartz Fst Op: op Fst add decomp
-- statement:
--   The Schwartz Fst Op construction uses the op Fst add decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L52-L59

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

theorem GlobalTheory.SchwartzFstOp.opFst_add_decomp (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by sorry
