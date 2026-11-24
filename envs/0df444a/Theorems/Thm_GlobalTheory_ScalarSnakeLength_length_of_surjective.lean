-- Prove2me | Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_of_surjective
-- name    : GlobalTheory.ScalarSnakeLength.length_of_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:34.119711+00:00
-- url     : https://prove2.me/theorems/bf1002a0-547c-46a4-8778-0d213f3b5694
-- title:
--   Scalar Snake Length: length of surjective
-- statement:
--   The Scalar Snake Length construction uses the length of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L29-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]

theorem GlobalTheory.ScalarSnakeLength.length_of_surjective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (g : N₁ →ₗ[A] N₂) (hg : Function.Surjective g) :
    Module.length A (LinearMap.range g) = Module.length A N₂ := by sorry
