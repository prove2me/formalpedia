-- Prove2me | Theorems.Thm_GlobalTheory_TensorUnitSpanTop_span_one_tmul_eq_top
-- name    : GlobalTheory.TensorUnitSpanTop.span_one_tmul_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:17.150525+00:00
-- url     : https://prove2.me/theorems/ea47c638-efdc-4e62-aaf6-a46347ba11f4
-- title:
--   Tensor Unit Span Top: span one tmul eq top
-- statement:
--   The Tensor Unit Span Top construction uses the span one tmul eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanOneTmulEqTop.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanOneTmulEqTop.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanOneTmulEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorUnitSpanTop
open TensorProduct

theorem GlobalTheory.TensorUnitSpanTop.span_one_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by sorry
