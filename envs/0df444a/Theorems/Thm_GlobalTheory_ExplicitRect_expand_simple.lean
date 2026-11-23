-- Prove2me | Theorems.Thm_GlobalTheory_ExplicitRect_expand_simple
-- name    : GlobalTheory.ExplicitRect.expand_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:08.1793+00:00
-- url     : https://prove2.me/theorems/1214e545-caf8-4da2-a8bf-7563cf849c7d
-- title:
--   Explicit Rect: expand simple
-- statement:
--   The Explicit Rect construction uses the expand simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AnalyticAtDslope.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AnalyticAtDslope.lean#L47-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect

theorem GlobalTheory.ExplicitRect.expand_simple {φ g : ℂ → ℂ} {p k : ℂ} {u : ℝ} (hu : 0 < u) (hp : p ≠ 0)
    (hg : AnalyticAt ℂ g p) (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ (a : ℂ) (G : ℂ → ℂ), AnalyticAt ℂ G p ∧ ∀ᶠ s in 𝓝[≠] p,
      -(φ s) * (u : ℂ) ^ s / s = a / (s - p) ^ 2 + (-(k * ((u : ℂ) ^ p / p))) / (s - p) + G s := by sorry
