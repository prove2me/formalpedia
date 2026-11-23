-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_norm_le_three
-- name    : GlobalTheory.PerronKernel.norm_le_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:14.542305+00:00
-- url     : https://prove2.me/theorems/137fb521-f6db-4702-97f0-e4cfa803c146
-- title:
--   Perron Kernel: norm le three
-- statement:
--   The Perron Kernel construction uses the norm le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L216-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L216-L226

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

theorem GlobalTheory.PerronKernel.norm_le_three {x p q r : ℂ} (h : I * x = p - q + I * r ∨ I * x = q - p + I * r) :
    ‖x‖ ≤ ‖p‖ + ‖q‖ + ‖r‖ := by sorry
