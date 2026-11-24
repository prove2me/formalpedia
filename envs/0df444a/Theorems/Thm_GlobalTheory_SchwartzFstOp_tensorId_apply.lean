-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_tensorId_apply
-- name    : GlobalTheory.SchwartzFstOp.tensorId_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:53.84496+00:00
-- url     : https://prove2.me/theorems/3268b420-6b3f-494e-b606-71af22011cd1
-- title:
--   Schwartz Fst Op: tensor Id apply
-- statement:
--   The Schwartz Fst Op construction uses the tensor Id apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzOperatorParametricExtension.lean#L242-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzOperatorParametricExtension.lean#L242-L243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzOperatorParametricExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [FiniteDimensional ℝ V']

theorem GlobalTheory.SchwartzFstOp.tensorId_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    tensorId T f (y, x') = T (sliceCLM x' f) y := by sorry
