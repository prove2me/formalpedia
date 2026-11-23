-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_constantCoeff_prim
-- name    : GlobalTheory.FormalLog.constantCoeff_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:44.492829+00:00
-- url     : https://prove2.me/theorems/3a3b17c3-5883-4aa7-8112-4f367ac25ada
-- title:
--   Formal Log: constant Coeff prim
-- statement:
--   The Formal Log construction uses the constant Coeff prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffPrim.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffPrim.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]

theorem GlobalTheory.FormalLog.constantCoeff_prim (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by sorry
