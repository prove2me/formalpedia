-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_measurable_cutFract
-- name    : GlobalTheory.ZetaHalfPlane.measurable_cutFract
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:39.025798+00:00
-- url     : https://prove2.me/theorems/8712b680-0e52-4d42-853d-547c07b6c128
-- title:
--   Zeta Half Plane: measurable cut Fract
-- statement:
--   The Zeta Half Plane construction uses the measurable cut Fract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L23-L24

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

theorem GlobalTheory.ZetaHalfPlane.measurable_cutFract : Measurable cutFract := by sorry
