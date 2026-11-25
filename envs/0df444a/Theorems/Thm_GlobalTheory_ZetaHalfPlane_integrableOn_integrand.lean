-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_integrableOn_integrand
-- name    : GlobalTheory.ZetaHalfPlane.integrableOn_integrand
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:43:36.481114+00:00
-- url     : https://prove2.me/theorems/90714fe8-2163-5df6-9b23-617d8514734b
-- title:
--   Zeta Half Plane: integrable On integrand
-- statement:
--   The Zeta Half Plane construction uses the integrable On integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L76-L80

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

theorem GlobalTheory.ZetaHalfPlane.integrableOn_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by sorry
