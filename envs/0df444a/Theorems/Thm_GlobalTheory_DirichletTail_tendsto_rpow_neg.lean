-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_tendsto_rpow_neg
-- name    : GlobalTheory.DirichletTail.tendsto_rpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:22.036121+00:00
-- url     : https://prove2.me/theorems/0e85ed89-0cda-49f0-84d3-8435da2e9d33
-- title:
--   Dirichlet Tail: tendsto rpow neg
-- statement:
--   The Dirichlet Tail construction uses the tendsto rpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L95-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology

theorem GlobalTheory.DirichletTail.tendsto_rpow_neg {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    Tendsto (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ)) atTop (𝓝 0) := by sorry
