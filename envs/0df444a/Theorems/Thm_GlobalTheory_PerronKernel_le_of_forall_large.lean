-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_le_of_forall_large
-- name    : GlobalTheory.PerronKernel.le_of_forall_large
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:10.995189+00:00
-- url     : https://prove2.me/theorems/ec61e805-2f6f-4163-aa98-611e11eb33e1
-- title:
--   Perron Kernel: le of forall large
-- statement:
--   The Perron Kernel construction uses the le of forall large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L208-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel

theorem GlobalTheory.PerronKernel.le_of_forall_large {x B K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (h : ∀ U : ℝ, c ≤ U → x ≤ B + K / U) : x ≤ B := by sorry
