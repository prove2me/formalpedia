-- Prove2me | Theorems.Thm_GlobalTheory_finite_away_of_isAlgebraic_of_finiteType
-- name    : GlobalTheory.finite_away_of_isAlgebraic_of_finiteType
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:17.566024+00:00
-- url     : https://prove2.me/theorems/dc19dca1-cbfb-41e3-83f2-f3828ac9f2b9
-- title:
--   Global Theory: finite away of is Algebraic of finite Type
-- statement:
--   The Global Theory construction uses the finite away of is Algebraic of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteAwayOfIsAlgebraicOfFiniteType.lean#L5-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteAwayOfIsAlgebraicOfFiniteType.lean#L5-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteAwayOfIsAlgebraicOfFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by sorry
