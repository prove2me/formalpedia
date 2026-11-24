-- Prove2me | Theorems.Thm_GlobalTheory_setIntegral_fderiv_eq_zero_of_lattice_periodic
-- name    : GlobalTheory.setIntegral_fderiv_eq_zero_of_lattice_periodic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:24.834402+00:00
-- url     : https://prove2.me/theorems/8a765b6b-256e-4ac5-8bf7-16e7d2c3f624
-- title:
--   Global Theory: set Integral fderiv eq zero of lattice periodic
-- statement:
--   The Global Theory construction uses the set Integral fderiv eq zero of lattice periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SetIntegralFderivEqZeroOfLatticePeriodic.lean#L33-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SetIntegralFderivEqZeroOfLatticePeriodic.lean#L33-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open MeasureTheory Module
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem GlobalTheory.setIntegral_fderiv_eq_zero_of_lattice_periodic
    (L : Submodule ℤ E) [Countable L] {D : Set E}
    (hD : IsAddFundamentalDomain L D μ) (hm : MeasurableSet D) (hb : Bornology.IsBounded D)
    {F : E → ℂ} (hF1 : ContDiff ℝ 1 F) (hF : ∀ (l : L) z, F (z + l) = F z) (v : E) :
    ∫ z in D, fderiv ℝ F z v ∂μ = 0 := by sorry
