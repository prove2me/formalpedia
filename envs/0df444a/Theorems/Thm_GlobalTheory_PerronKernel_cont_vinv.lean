-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_cont_vinv
-- name    : GlobalTheory.PerronKernel.cont_vinv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:10.009108+00:00
-- url     : https://prove2.me/theorems/6e4b126f-fe41-4f65-859c-0cc2a174de7b
-- title:
--   Perron Kernel: cont vinv
-- statement:
--   The Perron Kernel construction uses the cont vinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L16-L17

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

theorem GlobalTheory.PerronKernel.cont_vinv {σ : ℝ} (h : σ ≠ 0) : Continuous fun t : ℝ => ((σ : ℂ) + t * I)⁻¹ := by sorry
