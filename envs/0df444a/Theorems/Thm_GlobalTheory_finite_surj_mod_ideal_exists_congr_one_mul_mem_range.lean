-- Prove2me | Theorems.Thm_GlobalTheory_finite_surj_mod_ideal_exists_congr_one_mul_mem_range
-- name    : GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:19.323688+00:00
-- url     : https://prove2.me/theorems/f126ce04-da95-4caf-81fe-5683dd0c2069
-- title:
--   Global Theory: finite surj mod ideal exists congr one mul mem range
-- statement:
--   The Global Theory construction uses the finite surj mod ideal exists congr one mul mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSurjModIdealExistsCongrOneMulMemRange.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSurjModIdealExistsCongrOneMulMemRange.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory

theorem GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range :
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B,
      Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) →
      ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by sorry
