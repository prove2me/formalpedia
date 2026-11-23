-- Prove2me | Theorems.Thm_GroundTheory_Global_automorphismEquivRootsOfUnity_apply
-- name    : GroundTheory.Global.automorphismEquivRootsOfUnity_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:11.26849+00:00
-- url     : https://prove2.me/theorems/2a3bf672-602a-4fad-9035-e548e0efb207
-- title:
--   Global: automorphism Equiv Roots Of Unity apply
-- statement:
--   The Global construction uses the automorphism Equiv Roots Of Unity apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L118-L120

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
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
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
variable [CharZero F] {W : WeierstrassCurve F}
variable [W.IsElliptic]

theorem GroundTheory.Global.automorphismEquivRootsOfUnity_apply (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) :
    ((automorphismEquivRootsOfUnity hW ξ : Fˣ)) = ξ.1.u := by sorry

attribute [defeq] GroundTheory.Global.automorphismEquivRootsOfUnity_apply
