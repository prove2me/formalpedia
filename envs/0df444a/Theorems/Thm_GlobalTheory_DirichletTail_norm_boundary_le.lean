-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_norm_boundary_le
-- name    : GlobalTheory.DirichletTail.norm_boundary_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:16.3383+00:00
-- url     : https://prove2.me/theorems/291553a5-eecc-4f21-a7b4-c3c5231bce2c
-- title:
--   Dirichlet Tail: norm boundary le
-- statement:
--   The Dirichlet Tail construction uses the norm boundary le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L164-L169

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

theorem GlobalTheory.DirichletTail.norm_boundary_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (N : ℕ) :
    ‖(∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖
      ≤ q * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by sorry
