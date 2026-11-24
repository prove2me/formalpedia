-- Prove2me | Theorems.Thm_GlobalTheory_Desc_exists_pow_mul_mem_of_finiteType_away
-- name    : GlobalTheory.Desc.exists_pow_mul_mem_of_finiteType_away
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:28.794879+00:00
-- url     : https://prove2.me/theorems/e8d87753-9781-40f7-b508-9d3374a22da2
-- title:
--   Desc: exists pow mul mem of finite Type away
-- statement:
--   The Desc construction uses the exists pow mul mem of finite Type away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L38-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L38-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct

theorem GlobalTheory.Desc.exists_pow_mul_mem_of_finiteType_away {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by sorry
