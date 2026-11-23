-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral_of_trace
-- name    : GlobalTheory.HermClass.exists_int_mul_isIntegral_of_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:40.554829+00:00
-- url     : https://prove2.me/theorems/44d71b11-cdf2-45ac-b29c-42eca4802547
-- title:
--   Herm Class: exists int mul is Integral of trace
-- statement:
--   The Herm Class construction uses the exists int mul is Integral of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L40-L51

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable (E : Type) [Field E] [NumberField E]

theorem GlobalTheory.HermClass.exists_int_mul_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ a : E, (∀ t : E, IsIntegral ℤ t → ∃ m : ℤ, Algebra.trace ℚ E (a * t) = m) →
      IsIntegral ℤ ((D : E) * a) := by sorry
