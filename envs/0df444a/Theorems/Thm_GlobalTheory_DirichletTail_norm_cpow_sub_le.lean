-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_norm_cpow_sub_le
-- name    : GlobalTheory.DirichletTail.norm_cpow_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:42.793421+00:00
-- url     : https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965
-- title:
--   Dirichlet Tail: norm cpow sub le
-- statement:
--   The Dirichlet Tail construction uses the norm cpow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L57-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L57-L93

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

theorem GlobalTheory.DirichletTail.norm_cpow_sub_le {a b δ : ℝ} {s : ℂ} (ha : 1 ≤ a) (hab : a ≤ b) (hδ : 0 < δ)
    (hs : δ ≤ s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ / δ * (a ^ (-δ) - b ^ (-δ)) := by sorry
