-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_mulLeft_separable_of_adjoin_eq_of_reduced
-- name    : GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:29:07.757802+00:00
-- url     : https://prove2.me/theorems/d8d441e3-aefb-48d4-94e3-41d44e934a64
-- title:
--   T: charpoly mul Left separable of adjoin eq of reduced
-- statement:
--   The T construction uses the charpoly mul Left separable of adjoin eq of reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftSeparableOfAdjoinEqTopStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyMulLeftSeparableOfAdjoinEqTopStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A → (LinearMap.mulLeft E y).charpoly.Separable := by sorry
