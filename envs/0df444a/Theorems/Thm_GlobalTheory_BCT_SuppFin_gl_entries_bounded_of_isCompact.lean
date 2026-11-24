-- Prove2me | Theorems.Thm_GlobalTheory_BCT_SuppFin_gl_entries_bounded_of_isCompact
-- name    : GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:57.136398+00:00
-- url     : https://prove2.me/theorems/7a203c6a-084f-4fd9-a1c5-69fcd29deebc
-- title:
--   Supp Fin: gl entries bounded of is Compact
-- statement:
--   The Supp Fin construction uses the gl entries bounded of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L36-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompact.lean#L36-L63

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

theorem GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))),
    IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j,
      Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by sorry
