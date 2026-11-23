-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_interchange
-- name    : GlobalTheory.PerronPsi.interchange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:20.179609+00:00
-- url     : https://prove2.me/theorems/c1f67eec-90e7-4422-b5a6-4fd0cf56c499
-- title:
--   Perron Psi: interchange
-- statement:
--   The Perron Psi construction uses the interchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L70-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L70-L147

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

theorem GlobalTheory.PerronPsi.interchange (a : ℕ → ℂ) (ha0 : a 0 = 0) {c u : ℝ} (T : ℝ) (hc : 0 < c) (hu : 0 < u)
    (hs : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n * ∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      (∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I)
        / ((c : ℂ) + t * I)) := by sorry
