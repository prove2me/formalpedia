-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_compact_support_dense
-- name    : GlobalTheory.T.schwartz_compact_support_dense
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:29.324111+00:00
-- url     : https://prove2.me/theorems/331c9e75-5e9c-4338-84ee-c654163d13ca
-- title:
--   T: schwartz compact support dense
-- statement:
--   The T construction uses the schwartz compact support dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCompactSupportDenseStatement.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCompactSupportDenseStatement.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDenseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_compact_support_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by sorry
