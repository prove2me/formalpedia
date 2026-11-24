-- Prove2me | Theorems.Thm_GlobalTheory_exists_isPullback_of_factor_iff
-- name    : GlobalTheory.exists_isPullback_of_factor_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:15.877028+00:00
-- url     : https://prove2.me/theorems/793c0c76-2788-480a-a768-91a4056b1218
-- title:
--   Global Theory: exists is Pullback of factor iff
-- statement:
--   The Global Theory construction uses the exists is Pullback of factor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCover.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCover.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_isPullback_of_factor_iff {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by sorry
