-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_trace_mul_of_separable_generated
-- name    : GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:28.161727+00:00
-- url     : https://prove2.me/theorems/2a2e2140-c856-41dc-b9cc-5f0c1faf81f6
-- title:
--   T: eq zero of trace mul of separable generated
-- statement:
--   The T construction uses the eq zero of trace mul of separable generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGeneratedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGeneratedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGeneratedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) → ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by sorry
