-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_w_nonneg
-- name    : GlobalTheory.PerronPsi.w_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:25.597772+00:00
-- url     : https://prove2.me/theorems/cbfb73d4-bb05-4ef3-9885-0ccffb58cd60
-- title:
--   Perron Psi: w nonneg
-- statement:
--   The Perron Psi construction uses the w nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L213-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L213-L215

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

theorem GlobalTheory.PerronPsi.w_nonneg (N : ℕ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ w N B n := by sorry
