-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompact_GL_bounded_entries_completion_finitePlace
-- name    : GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:24.940813+00:00
-- url     : https://prove2.me/theorems/d3d48d58-6b16-48dc-aafb-9a4cd76314d3
-- title:
--   T: is Compact GL bounded entries completion finite Place
-- statement:
--   The T construction uses the is Compact GL bounded entries completion finite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by sorry
