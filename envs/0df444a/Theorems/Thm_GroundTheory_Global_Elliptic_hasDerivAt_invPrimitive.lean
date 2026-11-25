-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_invPrimitive
-- name    : GroundTheory.Global.Elliptic.hasDerivAt_invPrimitive
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:37.156675+00:00
-- url     : https://prove2.me/theorems/0e6af8ef-f8b0-46fe-b17f-6af1b5df6f7b
-- title:
--   Elliptic: has Deriv At inv Primitive
-- statement:
--   The Elliptic construction uses the has Deriv At inv Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L225-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L225-L248

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

theorem GroundTheory.Global.Elliptic.hasDerivAt_invPrimitive {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (invPrimitive c) ((x : ℂ) + c * I)⁻¹ x := by sorry
