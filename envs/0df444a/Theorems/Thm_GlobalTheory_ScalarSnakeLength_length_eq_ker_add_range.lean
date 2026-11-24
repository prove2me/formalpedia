-- Prove2me | Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_eq_ker_add_range
-- name    : GlobalTheory.ScalarSnakeLength.length_eq_ker_add_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:25.065629+00:00
-- url     : https://prove2.me/theorems/9e727317-5152-4fb0-8f11-39cb5aa0d9aa
-- title:
--   Scalar Snake Length: length eq ker add range
-- statement:
--   The Scalar Snake Length construction uses the length eq ker add range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L9-L15

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

theorem GlobalTheory.ScalarSnakeLength.length_eq_ker_add_range {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (φ : M →ₗ[A] P) :
    Module.length A M =
      Module.length A (LinearMap.ker φ) + Module.length A (LinearMap.range φ) := by sorry
