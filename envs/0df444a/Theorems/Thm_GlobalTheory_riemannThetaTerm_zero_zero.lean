-- Prove2me | Theorems.Thm_GlobalTheory_riemannThetaTerm_zero_zero
-- name    : GlobalTheory.riemannThetaTerm_zero_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:14.421003+00:00
-- url     : https://prove2.me/theorems/14c6ebfc-ae48-4d53-a597-c1f47800d0c2
-- title:
--   Global Theory: riemann Theta Term zero zero
-- statement:
--   The Global Theory construction uses the riemann Theta Term zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L247-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L247-L251

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem GlobalTheory.riemannThetaTerm_zero_zero (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm 0 0 Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) / 2 +
        (fun i => (n i : ℂ)) ⬝ᵥ v)) := by sorry
