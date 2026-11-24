-- Prove2me | Theorems.Thm_GlobalTheory_ZetaHalfPlane_fractInt_eq_mellin
-- name    : GlobalTheory.ZetaHalfPlane.fractInt_eq_mellin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:19.012838+00:00
-- url     : https://prove2.me/theorems/0ec3de19-8864-4321-ad00-61991bd32a0e
-- title:
--   Zeta Half Plane: fract Int eq mellin
-- statement:
--   The Zeta Half Plane construction uses the fract Int eq mellin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtFractInt.lean#L26-L37

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

theorem GlobalTheory.ZetaHalfPlane.fractInt_eq_mellin (s : ℂ) : fractInt s = mellin cutFract (-s) := by sorry
