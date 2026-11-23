-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_vinv
-- name    : GlobalTheory.PerronKernel.vinv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.636923+00:00
-- url     : https://prove2.me/theorems/80b9303c-0efc-4631-a6cd-f4fd6560dd86
-- title:
--   Perron Kernel: vinv
-- statement:
--   The Perron Kernel construction uses the vinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L44-L61

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

theorem GlobalTheory.PerronKernel.vinv {σ : ℝ} (h : σ ≠ 0) (T : ℝ) :
    ∫ t in (-T)..T, ((σ : ℂ) + t * I)⁻¹ = ((2 * Real.arctan (T / σ) : ℝ) : ℂ) := by sorry
