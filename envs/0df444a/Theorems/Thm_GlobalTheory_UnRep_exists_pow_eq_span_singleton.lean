-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_pow_eq_span_singleton
-- name    : GlobalTheory.UnRep.exists_pow_eq_span_singleton
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:05.905146+00:00
-- url     : https://prove2.me/theorems/296f4a06-4ec4-4ded-8360-c91628b0d77e
-- title:
--   Un Rep: exists pow eq span singleton
-- statement:
--   The Un Rep construction uses the exists pow eq span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsDenominatorPrimesPrescribed.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsDenominatorPrimesPrescribed.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.exists_pow_eq_span_singleton (E : Type) [Field E] [NumberField E] (a : Ideal (𝓞 E))
    (ha : a ≠ ⊥) : ∃ (h : ℕ) (s : 𝓞 E), h ≠ 0 ∧ a ^ h = Ideal.span {s} := by sorry
