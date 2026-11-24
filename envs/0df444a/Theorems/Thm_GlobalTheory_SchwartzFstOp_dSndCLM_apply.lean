-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_dSndCLM_apply
-- name    : GlobalTheory.SchwartzFstOp.dSndCLM_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:27.236687+00:00
-- url     : https://prove2.me/theorems/e6150710-4292-48ab-b614-e15737d8738a
-- title:
--   Schwartz Fst Op: d Snd CLM apply
-- statement:
--   The Schwartz Fst Op construction uses the d Snd CLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthProdMkConst.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthProdMkConst.lean#L65-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.SchwartzFstOp.dSndCLM_apply [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V')
    (v' : V') : dSndCLM T f p v' = opFst T (lineSnd v' f) p := by sorry
