-- Prove2me | Theorems.Thm_GlobalTheory_T_separated_of_finite_surjective_quotient
-- name    : GlobalTheory.T.separated_of_finite_surjective_quotient
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:25.563797+00:00
-- url     : https://prove2.me/theorems/24255332-47da-40c6-a71e-2a1d6ef7f7e8
-- title:
--   T: separated of finite surjective quotient
-- statement:
--   The T construction uses the separated of finite surjective quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotientStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotientStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotient
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotientStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.separated_of_finite_surjective_quotient : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by sorry
