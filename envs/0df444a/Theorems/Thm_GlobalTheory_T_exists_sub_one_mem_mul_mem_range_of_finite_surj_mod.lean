-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_sub_one_mem_mul_mem_range_of_finite_surj_mod
-- name    : GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:38.06682+00:00
-- url     : https://prove2.me/theorems/5c64105c-4abb-4a93-b309-33095e5725db
-- title:
--   T: exists sub one mem mul mem range of finite surj mod
-- statement:
--   The T construction uses the exists sub one mem mul mem range of finite surj mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSurjModIdealExistsCongrOneMulMemRangeStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSurjModIdealExistsCongrOneMulMemRangeStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRangeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B, Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) → ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by sorry
