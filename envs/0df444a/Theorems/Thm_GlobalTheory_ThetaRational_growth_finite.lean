-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_growth_finite
-- name    : GlobalTheory.ThetaRational.growth_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:20.273367+00:00
-- url     : https://prove2.me/theorems/99b2b711-dd79-4f80-b1de-83b3c286fb94
-- title:
--   Theta Rational: growth finite
-- statement:
--   The Theta Rational construction uses the growth finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L309-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L309-L319

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E : Type*} {n : ℕ}

theorem GlobalTheory.ThetaRational.growth_finite {ι : Type*} [Fintype ι] (x : E → ℝ) (hx : ∀ e, 1 ≤ x e) (u : ι → E → ℂ)
    (hu : ∀ c, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e, ‖u c e‖ ≤ C * x e ^ m) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e c, ‖u c e‖ ≤ C * x e ^ m := by sorry
