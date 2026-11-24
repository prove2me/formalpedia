-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_exists_tensorId
-- name    : GlobalTheory.SchwartzFstOp.exists_tensorId
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:54.270157+00:00
-- url     : https://prove2.me/theorems/28a4d102-b103-4fc4-a01c-4120fa5acc4a
-- title:
--   Schwartz Fst Op: exists tensor Id
-- statement:
--   The Schwartz Fst Op construction uses the exists tensor Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzOperatorParametricExtension.lean#L245-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzOperatorParametricExtension.lean#L245-L255

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

theorem GlobalTheory.SchwartzFstOp.exists_tensorId : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V')
      (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by sorry
