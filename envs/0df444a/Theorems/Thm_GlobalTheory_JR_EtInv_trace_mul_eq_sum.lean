-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtInv_trace_mul_eq_sum
-- name    : GlobalTheory.JR.EtInv.trace_mul_eq_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:07.543547+00:00
-- url     : https://prove2.me/theorems/ab768175-6023-4388-a3c3-dfa9560faaf0
-- title:
--   Et Inv: trace mul eq sum
-- statement:
--   The Et Inv construction uses the trace mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean#L31-L34

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
variable {r : ℕ} {τ : K}

theorem GlobalTheory.JR.EtInv.trace_mul_eq_sum (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by sorry
