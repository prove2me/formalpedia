-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_growth_mv
-- name    : GlobalTheory.ThetaRational.growth_mv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:07:07.086414+00:00
-- url     : https://prove2.me/theorems/6f96ebb1-2d52-43ea-9c92-05ce41d2d8b1
-- title:
--   Theta Rational: growth mv
-- statement:
--   The Theta Rational construction uses the growth mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L287-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L287-L307

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

theorem GlobalTheory.ThetaRational.growth_mv (q : MvPolynomial (Fin n) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin n → ℂ, ‖MvPolynomial.eval x q‖ ≤ C * (1 + ‖x‖) ^ m := by sorry
