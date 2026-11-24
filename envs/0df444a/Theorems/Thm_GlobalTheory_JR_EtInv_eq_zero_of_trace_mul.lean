-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtInv_eq_zero_of_trace_mul
-- name    : GlobalTheory.JR.EtInv.eq_zero_of_trace_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:08.788565+00:00
-- url     : https://prove2.me/theorems/a2678854-c3dd-47fc-a0f2-14c0c8c2d41a
-- title:
--   Et Inv: eq zero of trace mul
-- statement:
--   The Et Inv construction uses the eq zero of trace mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L14-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]

theorem GlobalTheory.JR.EtInv.eq_zero_of_trace_mul [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by sorry
