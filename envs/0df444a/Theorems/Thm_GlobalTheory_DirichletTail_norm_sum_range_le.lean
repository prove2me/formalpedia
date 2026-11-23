-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_norm_sum_range_le
-- name    : GlobalTheory.DirichletTail.norm_sum_range_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:18.634289+00:00
-- url     : https://prove2.me/theorems/7e91c151-5c10-41b2-8ff8-962bf6758f5e
-- title:
--   Dirichlet Tail: norm sum range le
-- statement:
--   The Dirichlet Tail construction uses the norm sum range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L8-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L8-L55

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

theorem GlobalTheory.DirichletTail.norm_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by sorry
