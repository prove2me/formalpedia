-- Prove2me | Theorems.Thm_GlobalTheory_BertiniC_no_dependence_of_general
-- name    : GlobalTheory.BertiniC.no_dependence_of_general
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:33.459911+00:00
-- url     : https://prove2.me/theorems/b64628f7-2bfa-42c5-8182-4bca38a2d706
-- title:
--   Bertini C: no dependence of general
-- statement:
--   The Bertini C construction uses the no dependence of general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BertiniGeneralMembersNoDerivativeRelation.lean#L72-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BertiniGeneralMembersNoDerivativeRelation.lean#L72-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BertiniC
open MvPolynomial

theorem GlobalTheory.BertiniC.no_dependence_of_general : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by sorry
