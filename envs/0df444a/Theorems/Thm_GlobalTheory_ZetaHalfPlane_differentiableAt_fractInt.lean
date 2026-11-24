-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_differentiableAt_fractInt
-- name    : GlobalTheory.ZetaHalfPlane.differentiableAt_fractInt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:31.158406+00:00
-- url     : https://prove2.me/theorems/53abce19-22e5-4efa-a0c5-0ca341eefaf2
-- title:
--   Zeta Half Plane: differentiable At fract Int
-- statement:
--   The Zeta Half Plane construction uses the differentiable At fract Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L39-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L39-L57

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

theorem GlobalTheory.ZetaHalfPlane.differentiableAt_fractInt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ fractInt s := by sorry
