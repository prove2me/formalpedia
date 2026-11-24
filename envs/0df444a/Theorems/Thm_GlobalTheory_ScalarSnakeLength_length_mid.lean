-- Prove2me | Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_mid
-- name    : GlobalTheory.ScalarSnakeLength.length_mid
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:31.02997+00:00
-- url     : https://prove2.me/theorems/2bce641d-17da-4544-9b28-2f716f062b23
-- title:
--   Scalar Snake Length: length mid
-- statement:
--   The Scalar Snake Length construction uses the length mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L17-L22

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

theorem GlobalTheory.ScalarSnakeLength.length_mid {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (h : Function.Exact f g) :
    Module.length A N₂ =
      Module.length A (LinearMap.range f) + Module.length A (LinearMap.range g) := by sorry
