-- Prove2me | Theorems.Thm_GlobalTheory_trace_eq_sum_coords_of_algEquiv
-- name    : GlobalTheory.trace_eq_sum_coords_of_algEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:29.545125+00:00
-- url     : https://prove2.me/theorems/edd06f12-b6c8-4c58-bd8f-117c469bf704
-- title:
--   Global Theory: trace eq sum coords of alg Equiv
-- statement:
--   The Global Theory construction uses the trace eq sum coords of alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceEqSumCoordsOfAlgEquiv.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceEqSumCoordsOfAlgEquiv.lean#L14-L16

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

theorem GlobalTheory.trace_eq_sum_coords_of_algEquiv {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by sorry
