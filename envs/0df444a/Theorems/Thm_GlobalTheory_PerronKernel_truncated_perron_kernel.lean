-- Prove2me | Theorems.Thm_GlobalTheory_PerronKernel_truncated_perron_kernel
-- name    : GlobalTheory.PerronKernel.truncated_perron_kernel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:39.952694+00:00
-- url     : https://prove2.me/theorems/676b3e73-7502-42f4-b2f6-63f1b91db080
-- title:
--   Perron Kernel: truncated perron kernel
-- statement:
--   The Perron Kernel construction uses the truncated perron kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L346-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronKernel.lean#L346-L402

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

theorem GlobalTheory.PerronKernel.truncated_perron_kernel : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → y ≠ 1 → 0 < c → 1 ≤ T → ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - (if 1 < y then 1 else 0)‖ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) := by sorry
