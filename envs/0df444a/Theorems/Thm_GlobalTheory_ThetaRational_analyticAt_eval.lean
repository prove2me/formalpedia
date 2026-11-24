-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_analyticAt_eval
-- name    : GlobalTheory.ThetaRational.analyticAt_eval
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:44.512379+00:00
-- url     : https://prove2.me/theorems/5d117b98-2ee6-4f00-bd9d-fa5c31c551f2
-- title:
--   Theta Rational: analytic At eval
-- statement:
--   The Theta Rational construction uses the analytic At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L340-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L340-L348

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

theorem GlobalTheory.ThetaRational.analyticAt_eval (r : Polynomial (MvPolynomial (Fin n) ℂ)) (w : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin n → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) w := by sorry
