-- Prove2me | Theorems.Thm_GlobalTheory_T_unit_real_of_sub_one_mem_span_prime
-- name    : GlobalTheory.T.unit_real_of_sub_one_mem_span_prime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:20.621418+00:00
-- url     : https://prove2.me/theorems/c91b9bcc-8e5c-40b6-9ce5-5c8a1977d685
-- title:
--   T: unit real of sub one mem span prime
-- statement:
--   The T construction uses the unit real of sub one mem span prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitRealOfCongrOneStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitRealOfCongrOneStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitRealOfCongrOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitRealOfCongrOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unit_real_of_sub_one_mem_span_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by sorry
