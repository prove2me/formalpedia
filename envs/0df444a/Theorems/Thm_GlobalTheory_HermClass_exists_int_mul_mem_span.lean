-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_mem_span
-- name    : GlobalTheory.HermClass.exists_int_mul_mem_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:16.46437+00:00
-- url     : https://prove2.me/theorems/5612e303-c3d2-4888-aee1-e42227fa00a6
-- title:
--   Herm Class: exists int mul mem span
-- statement:
--   The Herm Class construction uses the exists int mul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L53-L72

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

theorem GlobalTheory.HermClass.exists_int_mul_mem_span :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by sorry
