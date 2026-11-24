-- Prove2me | Theorems.Thm_GlobalTheory_TraceConj_exists_linearMap_of_trace_eq
-- name    : GlobalTheory.TraceConj.exists_linearMap_of_trace_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:11:03.616581+00:00
-- url     : https://prove2.me/theorems/5755e4c6-999a-402a-a347-7524ca505977
-- title:
--   Trace Conj: exists linear Map of trace eq
-- statement:
--   The Trace Conj construction uses the exists linear Map of trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L90-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L90-L114

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

theorem GlobalTheory.TraceConj.exists_linearMap_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hM : Submodule.span R (Set.range M) = ⊤) (hN : Submodule.span R (Set.range N) = ⊤) :
    ∃ φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R, φ 1 = 1 ∧ ∀ g X, φ (M g * X) = N g * φ X := by sorry
