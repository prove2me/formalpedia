-- Prove2me | Theorems.Thm_GlobalTheory_RiemannThetaModel_one_le_re_riemannTheta_I_smul_one
-- name    : GlobalTheory.RiemannThetaModel.one_le_re_riemannTheta_I_smul_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:08.817691+00:00
-- url     : https://prove2.me/theorems/aec2617d-5bd4-4246-b379-b92fa0cf384e
-- title:
--   Riemann Theta Model: one le re riemann Theta I smul one
-- statement:
--   The Riemann Theta Model construction uses the one le re riemann Theta I smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L66-L81

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

theorem GlobalTheory.RiemannThetaModel.one_le_re_riemannTheta_I_smul_one [DecidableEq ι] :
    1 ≤ (riemannTheta (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0).re := by sorry
