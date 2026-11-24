-- Prove2me | Theorems.Thm_GlobalTheory_TraceConj_span_top_of_residual
-- name    : GlobalTheory.TraceConj.span_top_of_residual
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:55.195519+00:00
-- url     : https://prove2.me/theorems/9d8a8189-dbea-4ecd-b1d8-a81c82f82c96
-- title:
--   Trace Conj: span top of residual
-- statement:
--   The Trace Conj construction uses the span top of residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L56-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLinearMapOfTraceEq.lean#L56-L88

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

theorem GlobalTheory.TraceConj.span_top_of_residual {Γ O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (M : Γ → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by sorry
