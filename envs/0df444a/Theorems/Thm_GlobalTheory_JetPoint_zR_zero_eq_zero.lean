-- Prove2me | Theorems.Thm_GlobalTheory_JetPoint_zR_zero_eq_zero
-- name    : GlobalTheory.JetPoint.zR_zero_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:08.82701+00:00
-- url     : https://prove2.me/theorems/bfe3ad1d-c592-41bf-a6d7-fd8d4a67c4b1
-- title:
--   Jet Point: z R zero eq zero
-- statement:
--   The Jet Point construction uses the z R zero eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetPointsOfIsLieBasis.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetPointsOfIsLieBasis.lean#L46-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetPoint
open GlobalTheory.SqZero
variable {R : Type} [CommRing R]

theorem GlobalTheory.JetPoint.zR_zero_eq_zero {κ : Type} (j : κ) : zR (R := R) 0 j = 0 := by sorry
