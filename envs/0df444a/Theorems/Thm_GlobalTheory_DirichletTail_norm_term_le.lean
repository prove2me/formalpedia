-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_norm_term_le
-- name    : GlobalTheory.DirichletTail.norm_term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:08.835979+00:00
-- url     : https://prove2.me/theorems/4123c382-065d-49a6-a055-3d2e32ca89bb
-- title:
--   Dirichlet Tail: norm term le
-- statement:
--   The Dirichlet Tail construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L138-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L138-L154

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

theorem GlobalTheory.DirichletTail.norm_term_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ)
    {δ R : ℝ} {s : ℂ} (hδ : 0 < δ) (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖term χ n s‖ ≤ q * (R / δ) *
      (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) := by sorry
