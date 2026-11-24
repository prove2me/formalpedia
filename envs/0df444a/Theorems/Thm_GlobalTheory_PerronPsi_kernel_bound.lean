-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_kernel_bound
-- name    : GlobalTheory.PerronPsi.kernel_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:29.577829+00:00
-- url     : https://prove2.me/theorems/1a186e9f-2ce7-451d-b203-faa1f6b62c54
-- title:
--   Perron Psi: kernel bound
-- statement:
--   The Perron Psi construction uses the kernel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L7-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi

theorem GlobalTheory.PerronPsi.kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → 0 < c → 1 ≤ T →
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ ≤ C * y ^ c ∧
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ * (T * |Real.log y|) ≤ C * y ^ c := by sorry
