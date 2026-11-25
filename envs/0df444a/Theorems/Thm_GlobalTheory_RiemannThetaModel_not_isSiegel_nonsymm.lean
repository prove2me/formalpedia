-- Prove2me | Theorems.Thm_GlobalTheory_RiemannThetaModel_not_isSiegel_nonsymm
-- name    : GlobalTheory.RiemannThetaModel.not_isSiegel_nonsymm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:21.257283+00:00
-- url     : https://prove2.me/theorems/32d2c012-9c5a-5891-b895-9f6b66a78aff
-- title:
--   Riemann Theta Model: not is Siegel nonsymm
-- statement:
--   The Riemann Theta Model construction uses the not is Siegel nonsymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/NormSqRiemannThetaMulExpPeriodic.lean#L40-L42

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

theorem GlobalTheory.RiemannThetaModel.not_isSiegel_nonsymm : ¬ IsSiegel !![I, 1; 0, I] := by sorry
