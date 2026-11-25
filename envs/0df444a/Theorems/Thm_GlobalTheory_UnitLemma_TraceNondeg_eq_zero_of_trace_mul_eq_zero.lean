-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TraceNondeg_eq_zero_of_trace_mul_eq_zero
-- name    : GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:31:55.417123+00:00
-- url     : https://prove2.me/theorems/b5c670f1-d4ba-4865-9954-b9d7fc624a2e
-- title:
--   Trace Nondeg: eq zero of trace mul eq zero
-- statement:
--   The Trace Nondeg construction uses the eq zero of trace mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L32-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TraceNondeg

theorem GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) →
    ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by sorry
