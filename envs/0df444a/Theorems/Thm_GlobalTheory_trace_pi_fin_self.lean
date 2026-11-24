-- Prove2me | Theorems.Thm_GlobalTheory_trace_pi_fin_self
-- name    : GlobalTheory.trace_pi_fin_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:25.374952+00:00
-- url     : https://prove2.me/theorems/800ed212-1d55-4eb2-b1da-2d6faa14fef0
-- title:
--   Global Theory: trace pi fin self
-- statement:
--   The Global Theory construction uses the trace pi fin self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceEqSumCoordsOfAlgEquiv.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceEqSumCoordsOfAlgEquiv.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceEqSumCoordsOfAlgEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.trace_pi_fin_self {F : Type} [Field F] (r : ℕ) (x : Fin r → F) :
    Algebra.trace F (Fin r → F) x = ∑ i, x i := by sorry
