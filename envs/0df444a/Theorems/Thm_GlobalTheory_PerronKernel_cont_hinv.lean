-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_cont_hinv
-- name    : GlobalTheory.PerronKernel.cont_hinv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:20.554801+00:00
-- url     : https://prove2.me/theorems/7c2235a5-4812-4458-a9ed-f8ce182a0b09
-- title:
--   Perron Kernel: cont hinv
-- statement:
--   The Perron Kernel construction uses the cont hinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L19-L20

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

theorem GlobalTheory.PerronKernel.cont_hinv {t : ℝ} (h : t ≠ 0) : Continuous fun σ : ℝ => ((σ : ℂ) + t * I)⁻¹ := by sorry
