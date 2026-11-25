-- Prove2me | Theorems.Thm_GlobalTheory_RiemannThetaModel_riemannTheta_not_constant
-- name    : GlobalTheory.RiemannThetaModel.riemannTheta_not_constant
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:33.316794+00:00
-- url     : https://prove2.me/theorems/a246058b-a210-4b82-80c1-7daf36abf148
-- title:
--   Riemann Theta Model: riemann Theta not constant
-- statement:
--   The Riemann Theta Model construction uses the riemann Theta not constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L112-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L112-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
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

theorem GlobalTheory.RiemannThetaModel.riemannTheta_not_constant :
    riemannTheta 0 0 !![I] ![(1 + I) / 2] ≠ riemannTheta 0 0 !![I] 0 := by sorry
