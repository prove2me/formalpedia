-- Prove2me | Theorems.Thm_GlobalTheory_T_isDVR_of_principal_prime_localization
-- name    : GlobalTheory.T.isDVR_of_principal_prime_localization
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:25.83095+00:00
-- url     : https://prove2.me/theorems/7debeea8-d7fc-42dc-8fa8-2bd6295a0d38
-- title:
--   T: is DVR of principal prime localization
-- statement:
--   The T construction uses the is DVR of principal prime localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrLocPrincipalPrimeStatement.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrLocPrincipalPrimeStatement.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrLocPrincipalPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrLocPrincipalPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isDVR_of_principal_prime_localization : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by sorry
