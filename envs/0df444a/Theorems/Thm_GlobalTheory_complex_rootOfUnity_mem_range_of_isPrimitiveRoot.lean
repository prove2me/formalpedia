-- Prove2me | Theorems.Thm_GlobalTheory_complex_rootOfUnity_mem_range_of_isPrimitiveRoot
-- name    : GlobalTheory.complex_rootOfUnity_mem_range_of_isPrimitiveRoot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:34.99414+00:00
-- url     : https://prove2.me/theorems/945715f8-5eb1-5757-a22a-3d8dccc0a5e9
-- title:
--   Global Theory: complex root Of Unity mem range of is Primitive Root
-- statement:
--   The Global Theory construction uses the complex root Of Unity mem range of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ComplexRootOfUnityMemRangeOfIsPrimitiveRoot.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ComplexRootOfUnityMemRangeOfIsPrimitiveRoot.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ComplexRootOfUnityMemRangeOfIsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.complex_rootOfUnity_mem_range_of_isPrimitiveRoot :
    ∀ (K : Type) [Field K] (s : K →+* ℂ) (n : ℕ) (ζ : K), 0 < n → IsPrimitiveRoot ζ n →
      ∀ z : ℂ, z ^ n = 1 → ∃ r : K, s r = z := by sorry
