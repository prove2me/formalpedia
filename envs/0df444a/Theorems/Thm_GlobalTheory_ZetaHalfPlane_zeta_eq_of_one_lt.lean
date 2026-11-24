-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_zeta_eq_of_one_lt
-- name    : GlobalTheory.ZetaHalfPlane.zeta_eq_of_one_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:46.990434+00:00
-- url     : https://prove2.me/theorems/071684a7-da4c-480e-a736-f0aef824420c
-- title:
--   Zeta Half Plane: zeta eq of one lt
-- statement:
--   The Zeta Half Plane construction uses the zeta eq of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L82-L90

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

theorem GlobalTheory.ZetaHalfPlane.zeta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by sorry
