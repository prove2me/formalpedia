-- Prove2me | Theorems.Thm_GlobalTheory_SpanQuotientTensor_span_mkQ_one_tmul
-- name    : GlobalTheory.SpanQuotientTensor.span_mkQ_one_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:39.595807+00:00
-- url     : https://prove2.me/theorems/c077eb62-db8c-4e5d-b7b2-6d7fc608ecb3
-- title:
--   Span Quotient Tensor: span mk Q one tmul
-- statement:
--   The Span Quotient Tensor construction uses the span mk Q one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanMkQOneTmul.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanMkQOneTmul.lean#L5-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanMkQOneTmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanQuotientTensor

theorem GlobalTheory.SpanQuotientTensor.span_mkQ_one_tmul {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by sorry
