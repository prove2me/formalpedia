-- Prove2me | Theorems.Thm_GlobalTheory_T_adjoin_eq_top_and_isReduced_of_charpoly_separable
-- name    : GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:42.342042+00:00
-- url     : https://prove2.me/theorems/05648456-768c-45a6-8992-8831d6ab0daa
-- title:
--   T: adjoin eq top and is Reduced of charpoly separable
-- statement:
--   The T construction uses the adjoin eq top and is Reduced of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
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

theorem GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable → Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A := by sorry
