-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_half_le_log
-- name    : GlobalTheory.PerronPsi.half_le_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:42.302547+00:00
-- url     : https://prove2.me/theorems/c3c7c495-fa20-4131-8bfa-0131f136ccbe
-- title:
--   Perron Psi: half le log
-- statement:
--   The Perron Psi construction uses the half le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L264-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L264-L267

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

theorem GlobalTheory.PerronPsi.half_le_log {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by sorry
