-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearSpanImage_multilinear_mem_span_image_partial
-- name    : GlobalTheory.MultilinearSpanImage.multilinear_mem_span_image_partial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:31.091434+00:00
-- url     : https://prove2.me/theorems/4d7ad24d-2299-4ed4-a544-01c4fac33cb6
-- title:
--   Multilinear Span Image: multilinear mem span image partial
-- statement:
--   The Multilinear Span Image construction uses the multilinear mem span image partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearMemSpanImagePartial.lean#L5-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearMemSpanImagePartial.lean#L5-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearMemSpanImagePartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultilinearSpanImage

theorem GlobalTheory.MultilinearSpanImage.multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap ℂ M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by sorry
