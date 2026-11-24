-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_iteratedFDeriv_tendsto_zero_cocompact
-- name    : GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:16.452938+00:00
-- url     : https://prove2.me/theorems/301c9904-e129-46b2-b187-efc553342e5c
-- title:
--   Global Theory: schwartz iterated FDeriv tendsto zero cocompact
-- statement:
--   The Global Theory construction uses the schwartz iterated FDeriv tendsto zero cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIteratedFDerivTendstoZeroCocompact.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIteratedFDerivTendstoZeroCocompact.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.schwartz_iteratedFDeriv_tendsto_zero_cocompact
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ) :
    Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by sorry
