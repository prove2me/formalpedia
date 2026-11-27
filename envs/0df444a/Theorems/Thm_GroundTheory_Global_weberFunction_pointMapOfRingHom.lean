-- Prove2me | Theorems.Thm_GroundTheory_Global_weberFunction_pointMapOfRingHom
-- name    : GroundTheory.Global.weberFunction_pointMapOfRingHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:51.254918+00:00
-- url     : https://prove2.me/theorems/877fed82-5562-5d10-9814-fe04d51a65a1
-- title:
--   Global: weber Function point Map Of Ring Hom
-- statement:
--   The Global construction uses the weber Function point Map Of Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L141-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L141-L160

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
variable {L : Type*} [Field L]

theorem GroundTheory.Global.weberFunction_pointMapOfRingHom (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by sorry
