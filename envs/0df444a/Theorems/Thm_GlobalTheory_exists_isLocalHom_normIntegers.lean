-- Prove2me | Theorems.Thm_GlobalTheory_exists_isLocalHom_normIntegers
-- name    : GlobalTheory.exists_isLocalHom_normIntegers
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:42.075746+00:00
-- url     : https://prove2.me/theorems/33462c4c-2a0c-4453-9766-4634dd2778e9
-- title:
--   Global Theory: exists is Local Hom norm Integers
-- statement:
--   The Global Theory construction uses the exists is Local Hom norm Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L475-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L475-L489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
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
universe u

theorem GlobalTheory.exists_isLocalHom_normIntegers {V K C : Type*} [CommRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [NormedField C] [IsUltrametricDist C] [Algebra K C]
    (h : ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) :
    ∃ φ : V →+* normIntegers C, IsLocalHom φ ∧
      ∀ a, (φ a : C) = algebraMap K C (algebraMap V K a) := by sorry
