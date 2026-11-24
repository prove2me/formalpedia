-- Prove2me | Theorems.Thm_GlobalTheory_finite_quotient_span_of_birational
-- name    : GlobalTheory.finite_quotient_span_of_birational
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:02.226397+00:00
-- url     : https://prove2.me/theorems/bfd47223-985c-40f9-8be8-b31a3f0d91f7
-- title:
--   Global Theory: finite quotient span of birational
-- statement:
--   The Global Theory construction uses the finite quotient span of birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L30-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L30-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]

theorem GlobalTheory.finite_quotient_span_of_birational
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b)
    {a : A} (ha : a ≠ 0) : Module.Finite A (B ⧸ Ideal.span {algebraMap A B a}) := by sorry
