-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_dense_hasCompactSupport
-- name    : GlobalTheory.schwartz_dense_hasCompactSupport
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:27.536829+00:00
-- url     : https://prove2.me/theorems/04c99021-a5af-425b-914a-c9032e3751b2
-- title:
--   Global Theory: schwartz dense has Compact Support
-- statement:
--   The Global Theory construction uses the schwartz dense has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDenseHasCompactSupport.lean#L9-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDenseHasCompactSupport.lean#L9-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDenseHasCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.schwartz_dense_hasCompactSupport :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {f : SchwartzMap V ℂ | HasCompactSupport (f : V → ℂ)} := by sorry
