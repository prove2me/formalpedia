-- Prove2me | Theorems.Thm_GlobalTheory_RiemannThetaModel_riemannThetaTerm_eq_thetaTerm
-- name    : GlobalTheory.RiemannThetaModel.riemannThetaTerm_eq_thetaTerm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:10.97711+00:00
-- url     : https://prove2.me/theorems/afdeb67a-30aa-45b5-9a24-c34c7e974752
-- title:
--   Riemann Theta Model: riemann Theta Term eq theta Term
-- statement:
--   The Riemann Theta Model construction uses the riemann Theta Term eq theta Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_riemannThetaTerm_eq_thetaTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.RiemannThetaModel.riemannThetaTerm_eq_thetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n = ReciprocityTheory.PTheta.thetaTerm a b v Ω n := by sorry
