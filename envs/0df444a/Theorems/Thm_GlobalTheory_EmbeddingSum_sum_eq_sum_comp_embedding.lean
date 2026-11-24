-- Prove2me | Theorems.Thm_GlobalTheory_EmbeddingSum_sum_eq_sum_comp_embedding
-- name    : GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:24.430551+00:00
-- url     : https://prove2.me/theorems/9e233218-3a9f-4919-b878-c6df17d01307
-- title:
--   Embedding Sum: sum eq sum comp embedding
-- statement:
--   The Embedding Sum construction uses the sum eq sum comp embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumEqSumCompEmbedding.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumEqSumCompEmbedding.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingSum

theorem GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding :
    ∀ {N j : ℕ} (e : Fin j ↪ Fin N) (f : Fin N → ℂ),
      (∀ c ∉ Set.range (⇑e : Fin j → Fin N), f c = (0 : ℂ)) →
      ∑ c : Fin N, f c = ∑ a : Fin j, f ((e : Fin j → Fin N) a) := by sorry
