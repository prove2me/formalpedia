-- Prove2me | Theorems.Thm_GroundTheory_Global_weberValue_of_ne_zero
-- name    : GroundTheory.Global.weberValue_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:45.529482+00:00
-- url     : https://prove2.me/theorems/d3f0bf99-118c-448c-9f70-672448fcf727
-- title:
--   Global: weber Value of ne zero
-- statement:
--   The Global construction uses the weber Value of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L70-L72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass

theorem GroundTheory.Global.weberValue_of_ne_zero {W : WeierstrassCurve F} (ha : W.a₄ ≠ 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₂ W * g₃ W / W.Δ * x := by sorry
