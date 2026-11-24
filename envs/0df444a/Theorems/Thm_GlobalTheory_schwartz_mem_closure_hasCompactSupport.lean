-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_mem_closure_hasCompactSupport
-- name    : GlobalTheory.schwartz_mem_closure_hasCompactSupport
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:54.323582+00:00
-- url     : https://prove2.me/theorems/c2b33994-9937-41b5-b7e9-d28b37112b2b
-- title:
--   Global Theory: schwartz mem closure has Compact Support
-- statement:
--   The Global Theory construction uses the schwartz mem closure has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCompactSupportDense.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCompactSupportDense.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDenseHasCompactSupport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCompactSupportDense
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
open GlobalTheory

theorem GlobalTheory.schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by sorry
