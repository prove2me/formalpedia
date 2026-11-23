-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_im
-- name    : GlobalTheory.PerronKernel.ne_zero_of_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:02.578817+00:00
-- url     : https://prove2.me/theorems/a0657c41-2ca9-4bce-a3de-2c0b7960af67
-- title:
--   Perron Kernel: ne zero of im
-- statement:
--   The Perron Kernel construction uses the ne zero of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L11-L14

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

theorem GlobalTheory.PerronKernel.ne_zero_of_im {σ t : ℝ} (h : t ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by sorry
