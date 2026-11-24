-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_automorphismPoint_of_scale
-- name    : GroundTheory.Global.exists_automorphismPoint_of_scale
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:14.944624+00:00
-- url     : https://prove2.me/theorems/4c8ef070-8608-4f3e-9514-7f13da6f4f0b
-- title:
--   Global: exists automorphism Point of scale
-- statement:
--   The Global construction uses the exists automorphism Point of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L186-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L186-L201

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
variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]
omit [W.IsElliptic]

theorem GroundTheory.Global.exists_automorphismPoint_of_scale (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by sorry
