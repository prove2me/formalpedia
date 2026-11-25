-- Prove2me | Theorems.Thm_GlobalTheory_T_isPrimitiveTuple_of_linearIndependent_finite_ring
-- name    : GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:45:49.611283+00:00
-- url     : https://prove2.me/theorems/52c0475e-c47b-4c84-af92-724795563fca
-- title:
--   T: is Primitive Tuple of linear Independent finite ring
-- statement:
--   The T construction uses the is Primitive Tuple of linear Independent finite ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRingStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRingStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by sorry
