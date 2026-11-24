-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_ofReal_add_mul_I_ne_zero
-- name    : GroundTheory.Global.Elliptic.ofReal_add_mul_I_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:37.058268+00:00
-- url     : https://prove2.me/theorems/675c71b2-8505-4e6c-b920-86715766090a
-- title:
--   Elliptic: of Real add mul I ne zero
-- statement:
--   The Elliptic construction uses the of Real add mul I ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L220-L223

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GroundTheory.Global.Elliptic.ofReal_add_mul_I_ne_zero {c : ℝ} (hc : c ≠ 0) (x : ℝ) : (x : ℂ) + c * I ≠ 0 := by sorry
