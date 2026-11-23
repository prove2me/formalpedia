-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_hasSum_telescope
-- name    : GlobalTheory.DirichletTail.hasSum_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:00.551284+00:00
-- url     : https://prove2.me/theorems/2cf14248-638c-43be-8b95-74a905309ff0
-- title:
--   Dirichlet Tail: has Sum telescope
-- statement:
--   The Dirichlet Tail construction uses the has Sum telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L101-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L101-L121

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

theorem GlobalTheory.DirichletTail.hasSum_telescope {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    HasSum (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ) - ((n + N + 1 + 1 : ℕ) : ℝ) ^ (-δ))
      (((N + 1 : ℕ) : ℝ) ^ (-δ)) := by sorry
