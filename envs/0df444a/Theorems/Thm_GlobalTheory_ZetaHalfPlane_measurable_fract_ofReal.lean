-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_measurable_fract_ofReal
-- name    : GlobalTheory.ZetaHalfPlane.measurable_fract_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:24.204405+00:00
-- url     : https://prove2.me/theorems/c6a44f46-0ea2-450e-a7ff-2ee3b7a4cab2
-- title:
--   Zeta Half Plane: measurable fract of Real
-- statement:
--   The Zeta Half Plane construction uses the measurable fract of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane

theorem GlobalTheory.ZetaHalfPlane.measurable_fract_ofReal : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) := by sorry
