-- Prove2me | Theorems.Thm_GlobalTheory_T_valued_v_map_irreducible_eq_ofAdd_neg_one
-- name    : GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:17.197154+00:00
-- url     : https://prove2.me/theorems/7c7053d3-d09f-57ed-8858-dc479cb67358
-- title:
--   T: valued v map irreducible eq of Add neg one
-- statement:
--   The T construction uses the valued v map irreducible eq of Add neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdicCompletionValuationMapUniformiserStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdicCompletionValuationMapUniformiserStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiser
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiserStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by sorry
