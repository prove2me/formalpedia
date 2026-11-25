-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearSpanImage_multilinear_apply_mem_span_image
-- name    : GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:34.943195+00:00
-- url     : https://prove2.me/theorems/b1663e4f-e567-43b2-b962-129e2f7066cd
-- title:
--   Multilinear Span Image: multilinear apply mem span image
-- statement:
--   The Multilinear Span Image construction uses the multilinear apply mem span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearMemSpanImagePartial.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearMemSpanImagePartial.lean#L33-L39

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

theorem GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap ℂ M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} := by sorry
