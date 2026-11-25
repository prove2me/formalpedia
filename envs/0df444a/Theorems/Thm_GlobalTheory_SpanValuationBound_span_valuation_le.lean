-- Prove2me | Theorems.Thm_GlobalTheory_SpanValuationBound_span_valuation_le
-- name    : GlobalTheory.SpanValuationBound.span_valuation_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:48.674362+00:00
-- url     : https://prove2.me/theorems/fc48b1e7-3edc-41fd-b3da-cb9f23a0d11a
-- title:
--   Span Valuation Bound: span valuation le
-- statement:
--   The Span Valuation Bound construction uses the span valuation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanValuationLe.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanValuationLe.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanValuationLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanValuationBound
open IsDedekindDomain

theorem GlobalTheory.SpanValuationBound.span_valuation_le {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by sorry
