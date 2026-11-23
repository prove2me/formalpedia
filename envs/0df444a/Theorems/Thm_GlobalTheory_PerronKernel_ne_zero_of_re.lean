-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_re
-- name    : GlobalTheory.PerronKernel.ne_zero_of_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:36.51447+00:00
-- url     : https://prove2.me/theorems/e237b4c3-1dc0-48c4-9725-08b89eb69375
-- title:
--   Perron Kernel: ne zero of re
-- statement:
--   The Perron Kernel construction uses the ne zero of re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L6-L9

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

theorem GlobalTheory.PerronKernel.ne_zero_of_re {σ t : ℝ} (h : σ ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by sorry
