-- Prove2me | Theorems.Thm_GlobalTheory_bilinForm_bijective_of_nondegenerate_mod
-- name    : GlobalTheory.bilinForm_bijective_of_nondegenerate_mod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:41.439831+00:00
-- url     : https://prove2.me/theorems/d1c99654-a78a-40cc-af4b-4769b7295e07
-- title:
--   Global Theory: bilin Form bijective of nondegenerate mod
-- statement:
--   The Global Theory construction uses the bilin Form bijective of nondegenerate mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/BilinFormBijectiveOfNondegenerateMod.lean#L8-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/BilinFormBijectiveOfNondegenerateMod.lean#L8-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_BilinFormBijectiveOfNondegenerateMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.bilinForm_bijective_of_nondegenerate_mod (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by sorry
