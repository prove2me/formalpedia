-- Prove2me | Theorems.Thm_GlobalTheory_charpoly_mulLeft_separable_of_adjoin_eq_top
-- name    : GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:44.483736+00:00
-- url     : https://prove2.me/theorems/decf1b1b-23d4-43ad-9598-1dd0c0740c0d
-- title:
--   Global Theory: charpoly mul Left separable of adjoin eq top
-- statement:
--   The Global Theory construction uses the charpoly mul Left separable of adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftSeparableOfAdjoinEqTop.lean#L6-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftSeparableOfAdjoinEqTop.lean#L6-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by sorry
