-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_abel
-- name    : GlobalTheory.DirichletTail.abel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:21.041056+00:00
-- url     : https://prove2.me/theorems/62ed13be-f415-4bd1-9bc9-cee41cbe52aa
-- title:
--   Dirichlet Tail: abel
-- statement:
--   The Dirichlet Tail construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L127-L136

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

theorem GlobalTheory.DirichletTail.abel {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range N, term χ n s
        + (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by sorry
