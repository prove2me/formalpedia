-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_norm_exp
-- name    : GlobalTheory.PerronKernel.norm_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:17.177452+00:00
-- url     : https://prove2.me/theorems/b1060c6e-2c67-4daf-9c66-4fb931354ff3
-- title:
--   Perron Kernel: norm exp
-- statement:
--   The Perron Kernel construction uses the norm exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L75-L77

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

theorem GlobalTheory.PerronKernel.norm_exp (L σ t : ℝ) : ‖cexp (L * ((σ : ℂ) + t * I))‖ = Real.exp (L * σ) := by sorry
