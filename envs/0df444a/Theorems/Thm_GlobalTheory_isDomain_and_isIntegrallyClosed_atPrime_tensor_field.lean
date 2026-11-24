-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_tensor_field
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:47.552337+00:00
-- url     : https://prove2.me/theorems/de9f7588-0491-46e6-9c30-b4cf78f72a31
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime tensor field
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime tensor field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L51-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L51-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field
    (hL1 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K),
      ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R)
    (hL2 : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime],
      (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
        ∀ (q : Ideal C) [q.IsPrime],
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A],
      (∀ (P : Ideal A) [P.IsPrime],
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime],
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by sorry
