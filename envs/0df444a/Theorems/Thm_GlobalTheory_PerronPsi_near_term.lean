-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_near_term
-- name    : GlobalTheory.PerronPsi.near_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:30.325947+00:00
-- url     : https://prove2.me/theorems/caf3f861-b6bd-4021-aa77-b05b9642a18e
-- title:
--   Perron Psi: near term
-- statement:
--   The Perron Psi construction uses the near term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L321-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L321-L434

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

theorem GlobalTheory.PerronPsi.near_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h0 : E ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf1 : u / 2 < n) (hf2 : n < 2 * u) :
    Real.log n * E ≤ C * (16 * Real.log u * w ⌊u⌋₊ (2 * u / T) n) := by sorry
