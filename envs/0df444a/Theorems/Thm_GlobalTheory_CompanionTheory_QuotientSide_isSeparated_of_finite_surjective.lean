-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotientSide_isSeparated_of_finite_surjective
-- name    : GlobalTheory.CompanionTheory.QuotientSide.isSeparated_of_finite_surjective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:08.016961+00:00
-- url     : https://prove2.me/theorems/59284d49-b4c0-4869-99c6-12dce4377be9
-- title:
--   Quotient Side: is Separated of finite surjective
-- statement:
--   The Quotient Side construction uses the is Separated of finite surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotient.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/SeparatedOfFiniteSurjectiveQuotient.lean#L9-L33

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

theorem GlobalTheory.CompanionTheory.QuotientSide.isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by sorry
