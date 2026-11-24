-- Prove2me | Theorems.Thm_GlobalTheory_Desc_finiteType_away_of_pow_mul_mem
-- name    : GlobalTheory.Desc.finiteType_away_of_pow_mul_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:46.858799+00:00
-- url     : https://prove2.me/theorems/e8eae4e3-5695-4360-aece-081eff1fee49
-- title:
--   Desc: finite Type away of pow mul mem
-- statement:
--   The Desc construction uses the finite Type away of pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L7-L36

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

theorem GlobalTheory.Desc.finiteType_away_of_pow_mul_mem {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by sorry
