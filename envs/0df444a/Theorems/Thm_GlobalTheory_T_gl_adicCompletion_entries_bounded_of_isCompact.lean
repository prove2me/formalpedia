-- Prove2me | Theorems.Thm_GlobalTheory_T_gl_adicCompletion_entries_bounded_of_isCompact
-- name    : GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:37.655947+00:00
-- url     : https://prove2.me/theorems/fa811509-95a1-4541-9c64-e790bc3a2f50
-- title:
--   T: gl adic Completion entries bounded of is Compact
-- statement:
--   The T construction uses the gl adic Completion entries bounded of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompactStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlAdicCompletionEntriesBoundedOfIsCompactStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by sorry
