-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_prim_of_indep_of_isPrimitive
-- name    : GlobalTheory.GramCount.prim_of_indep_of_isPrimitive
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:10.824802+00:00
-- url     : https://prove2.me/theorems/8220070b-4897-42ad-a44f-3b5ef8de2a89
-- title:
--   Gram Count: prim of indep of is Primitive
-- statement:
--   The Gram Count construction uses the prim of indep of is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRing.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrimitiveTupleOfLinearIndependentFiniteRing.lean#L56-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrimitiveTupleOfLinearIndependentFiniteRing
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
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.prim_of_indep_of_isPrimitive : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive →
    ∀ (k n : ℕ) (x : Fin k → Fin n → B),
      (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by sorry
