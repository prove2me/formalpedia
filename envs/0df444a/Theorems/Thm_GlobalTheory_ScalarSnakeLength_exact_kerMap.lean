-- Prove2me | Theorems.Thm_GlobalTheory_ScalarSnakeLength_exact_kerMap
-- name    : GlobalTheory.ScalarSnakeLength.exact_kerMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:13.447164+00:00
-- url     : https://prove2.me/theorems/7160d52d-f234-48cd-84a9-3327a27b46c9
-- title:
--   Scalar Snake Length: exact ker Map
-- statement:
--   The Scalar Snake Length construction uses the exact ker Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthEqKerAddRange.lean#L66-L79

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
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

theorem GlobalTheory.ScalarSnakeLength.exact_kerMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (kerMap f b) (kerMap g b) := by sorry
