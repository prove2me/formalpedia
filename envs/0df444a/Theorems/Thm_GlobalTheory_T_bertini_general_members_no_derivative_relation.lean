-- Prove2me | Theorems.Thm_GlobalTheory_T_bertini_general_members_no_derivative_relation
-- name    : GlobalTheory.T.bertini_general_members_no_derivative_relation
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:26:11.704973+00:00
-- url     : https://prove2.me/theorems/399c80de-152a-48e6-924c-4a03a237839b
-- title:
--   T: bertini general members no derivative relation
-- statement:
--   The T construction uses the bertini general members no derivative relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BertiniGeneralMembersNoDerivativeRelationStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BertiniGeneralMembersNoDerivativeRelationStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.bertini_general_members_no_derivative_relation : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by sorry
