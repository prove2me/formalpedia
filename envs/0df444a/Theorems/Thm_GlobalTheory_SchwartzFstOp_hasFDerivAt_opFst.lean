-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_hasFDerivAt_opFst
-- name    : GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:57.746903+00:00
-- url     : https://prove2.me/theorems/9dcfe3a5-7705-498a-afd1-0393cf67673b
-- title:
--   Schwartz Fst Op: has FDeriv At op Fst
-- statement:
--   The Schwartz Fst Op construction uses the has FDeriv At op Fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L61-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFderivAtSchwartzOperatorFirst.lean#L61-L111

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

theorem GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ))
    (y : W) (x' : V') :
    HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')
      + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by sorry
