-- Prove2me | Theorems.Thm_GlobalTheory_BCT_SuppFin_exists_bound_of_isCompact
-- name    : GlobalTheory.BCT.SuppFin.exists_bound_of_isCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:45.656799+00:00
-- url     : https://prove2.me/theorems/1cff40f7-080e-4043-b269-12a8515ea5f8
-- title:
--   Supp Fin: exists bound of is Compact
-- statement:
--   The Supp Fin construction uses the exists bound of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L24-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
noncomputable section
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.SuppFin
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.BCT.SuppFin.exists_bound_of_isCompact (w : HeightOneSpectrum (𝓞 E)) {K : Set (w.adicCompletion E)}
    (hK : IsCompact K) : ∃ N : ℤ, ∀ z ∈ K, Valued.v z ≤ WithZero.exp N := by sorry
