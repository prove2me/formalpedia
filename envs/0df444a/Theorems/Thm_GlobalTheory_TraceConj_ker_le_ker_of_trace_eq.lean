-- Prove2me | Theorems.Thm_GlobalTheory_TraceConj_ker_le_ker_of_trace_eq
-- name    : GlobalTheory.TraceConj.ker_le_ker_of_trace_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:35.715954+00:00
-- url     : https://prove2.me/theorems/110f2a6f-a93c-4ee3-8714-dcafd6cdeaa6
-- title:
--   Trace Conj: ker le ker of trace eq
-- statement:
--   The Trace Conj construction uses the ker le ker of trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLinearMapOfTraceEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceConj
open IsLocalRing

theorem GlobalTheory.TraceConj.ker_le_ker_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span R (Set.range N) = ⊤) :
    LinearMap.ker (Finsupp.linearCombination R (fun g => M g)) ≤
      LinearMap.ker (Finsupp.linearCombination R (fun g => N g)) := by sorry
