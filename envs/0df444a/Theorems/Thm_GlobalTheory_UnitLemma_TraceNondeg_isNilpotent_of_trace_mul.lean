-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TraceNondeg_isNilpotent_of_trace_mul
-- name    : GlobalTheory.UnitLemma.TraceNondeg.isNilpotent_of_trace_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:46.148157+00:00
-- url     : https://prove2.me/theorems/e0debaa7-a508-405b-b171-50805ca1043b
-- title:
--   Trace Nondeg: is Nilpotent of trace mul
-- statement:
--   The Trace Nondeg construction uses the is Nilpotent of trace mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L11-L24

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

theorem GlobalTheory.UnitLemma.TraceNondeg.isNilpotent_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by sorry
