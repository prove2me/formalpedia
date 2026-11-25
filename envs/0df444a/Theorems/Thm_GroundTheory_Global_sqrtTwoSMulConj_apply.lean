-- Prove2me | Theorems.Thm_GroundTheory_Global_sqrtTwoSMulConj_apply
-- name    : GroundTheory.Global.sqrtTwoSMulConj_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:23.51885+00:00
-- url     : https://prove2.me/theorems/002017ff-9bf2-4348-b55b-c968f0c66136
-- title:
--   Global: sqrt Two SMul Conj apply
-- statement:
--   The Global construction uses the sqrt Two SMul Conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L65-L65

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.sqrtTwoSMulConj_apply (z : ℂ) : sqrtTwoSMulConj z = (√2 : ℝ) • conj z := by sorry
