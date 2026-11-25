-- Prove2me | Theorems.Thm_GlobalTheory_SpanValuationBound_main
-- name    : GlobalTheory.SpanValuationBound.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:43.977857+00:00
-- url     : https://prove2.me/theorems/4eebf06d-356e-4412-bc2d-ce14abaf1cf7
-- title:
--   Span Valuation Bound: main
-- statement:
--   The Span Valuation Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanValuationLe.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SpanValuationLe.lean#L24-L25

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

theorem GlobalTheory.SpanValuationBound.main : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {S : Set L} (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}, (∀ x ∈ S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) → ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by sorry
