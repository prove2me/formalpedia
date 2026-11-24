-- Prove2me | Theorems.Thm_GlobalTheory_T_frobeniusSubalgebra_counital_comul
-- name    : GlobalTheory.T.frobeniusSubalgebra_counital_comul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:40:47.368795+00:00
-- url     : https://prove2.me/theorems/80cc43e7-5eed-48b6-b780-94f318468831
-- title:
--   T: frobenius Subalgebra counital comul
-- statement:
--   The T construction uses the frobenius Subalgebra counital comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSubalgebraCounitalComulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusSubalgebraCounitalComulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusSubalgebraCounitalComulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.frobeniusSubalgebra_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by sorry
