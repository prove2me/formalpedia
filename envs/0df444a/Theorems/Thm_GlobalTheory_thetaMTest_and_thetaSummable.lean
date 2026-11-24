-- Prove2me | Theorems.Thm_GlobalTheory_thetaMTest_and_thetaSummable
-- name    : GlobalTheory.thetaMTest_and_thetaSummable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:01.524607+00:00
-- url     : https://prove2.me/theorems/ceaeee30-8f0d-42ca-93db-7cb179d58f6f
-- title:
--   Global Theory: theta MTest and theta Summable
-- statement:
--   The Global Theory construction uses the theta MTest and theta Summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMulDotProductLeOfIsCompactThetaDomain.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsMulDotProductLeOfIsCompactThetaDomain.lean#L117-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix ReciprocityTheory.PTheta
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
open Complex Matrix
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.thetaMTest_and_thetaSummable : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement ∧ _root_.ReciprocityTheory.PTheta.ThetaSummableStatement := by sorry
