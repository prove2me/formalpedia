-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotientSide_isSeparated_target_of_finite_surjective
-- name    : GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:33.705691+00:00
-- url     : https://prove2.me/theorems/56ba2fa9-a73b-4d67-9bc9-489c997ab5b1
-- title:
--   Quotient Side: is Separated target of finite surjective
-- statement:
--   The Quotient Side construction uses the is Separated target of finite surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotient.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotient.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotientSide

theorem GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by sorry
