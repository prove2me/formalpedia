-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_far_term
-- name    : GlobalTheory.PerronPsi.far_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:26.057554+00:00
-- url     : https://prove2.me/theorems/ed1adab0-1143-4c12-8704-120b6faffa11
-- title:
--   Perron Psi: far term
-- statement:
--   The Perron Psi construction uses the far term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L269-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L269-L319

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

theorem GlobalTheory.PerronPsi.far_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hn : 0 < n) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    Real.log n * E ≤ C * (12 * u * Real.log u / T
      * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))) := by sorry
