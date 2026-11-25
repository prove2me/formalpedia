-- Prove2me | Theorems.Thm_GlobalTheory_T_isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt
-- name    : GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:20.753414+00:00
-- url     : https://prove2.me/theorems/eeb964fb-5961-4ca3-bc13-b384ae7c17d7
-- title:
--   T: is Domain and is Integrally Closed at Prime tensor field alt
-- statement:
--   The T construction uses the is Domain and is Integrally Closed at Prime tensor field alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldAStatement
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

theorem GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by sorry
