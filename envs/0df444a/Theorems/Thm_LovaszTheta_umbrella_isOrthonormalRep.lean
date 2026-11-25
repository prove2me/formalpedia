-- Prove2me | Theorems.Thm_LovaszTheta_umbrella_isOrthonormalRep
-- name    : LovaszTheta.umbrella_isOrthonormalRep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:47:04.643694+00:00
-- url     : https://prove2.me/theorems/0f5cb4a2-fb50-4bb7-9eaa-f00d50b0b5a8
-- title:
--   Lovasz Theta: umbrella is Orthonormal Rep
-- statement:
--   The Lovasz Theta construction uses the umbrella is Orthonormal Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L205-L212
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L205-L212

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.umbrella_isOrthonormalRep : IsOrthonormalRep (cycleGraph 5) umbrella := by sorry
