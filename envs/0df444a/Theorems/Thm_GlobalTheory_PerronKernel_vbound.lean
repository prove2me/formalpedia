-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_vbound
-- name    : GlobalTheory.PerronKernel.vbound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:11.38474+00:00
-- url     : https://prove2.me/theorems/9b80146e-8361-40c4-9a3c-2f5f49caabcc
-- title:
--   Perron Kernel: vbound
-- statement:
--   The Perron Kernel construction uses the vbound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L79-L89

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

theorem GlobalTheory.PerronKernel.vbound (L : ℝ) {σ T : ℝ} (h : σ ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, cexp (L * ((σ : ℂ) + t * I)) / ((σ : ℂ) + t * I)‖
      ≤ Real.exp (L * σ) / |σ| * (2 * T) := by sorry
