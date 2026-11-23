-- Prove2me | Theorems.Thm_GroundTheory_Global_sqrtTwoSMulComplex_apply
-- name    : GroundTheory.Global.sqrtTwoSMulComplex_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:20.703181+00:00
-- url     : https://prove2.me/theorems/bbe8a28d-3fe4-4055-9a55-ac24ccfba19f
-- title:
--   Global: sqrt Two SMul Complex apply
-- statement:
--   The Global construction uses the sqrt Two SMul Complex apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L56-L56

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

theorem GroundTheory.Global.sqrtTwoSMulComplex_apply (z : ℂ) : sqrtTwoSMulComplex z = (√2 : ℝ) • z := by sorry
