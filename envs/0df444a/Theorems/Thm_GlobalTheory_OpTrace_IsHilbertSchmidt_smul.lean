-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_IsHilbertSchmidt_smul
-- name    : GlobalTheory.OpTrace.IsHilbertSchmidt.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:32.18615+00:00
-- url     : https://prove2.me/theorems/6067dc24-79c3-4e4d-9827-e8afae1b7bbe
-- title:
--   Is Hilbert Schmidt: smul
-- statement:
--   The Is Hilbert Schmidt construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L118-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
omit [CompleteSpace K]

theorem GlobalTheory.OpTrace.IsHilbertSchmidt.smul {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (c : ℂ) :
    IsHilbertSchmidt (c • T) := by sorry
