-- Prove2me | Theorems.Thm_GlobalTheory_RiemannThetaModel_siegelUpperHalfSpace_eq_siegelH
-- name    : GlobalTheory.RiemannThetaModel.siegelUpperHalfSpace_eq_siegelH
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:10.963588+00:00
-- url     : https://prove2.me/theorems/910a88b1-5b4c-5a7b-a37d-6da61623d6b7
-- title:
--   Riemann Theta Model: siegel Upper Half Space eq siegel H
-- statement:
--   The Riemann Theta Model construction uses the siegel Upper Half Space eq siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L25-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_siegelUpperHalfSpace_eq_siegelH

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

theorem GlobalTheory.RiemannThetaModel.siegelUpperHalfSpace_eq_siegelH :
    siegelUpperHalfSpace ι = ReciprocityTheory.PTheta.SiegelH ι := by sorry
