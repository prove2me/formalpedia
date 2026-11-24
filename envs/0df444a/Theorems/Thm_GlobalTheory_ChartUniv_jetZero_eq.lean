-- Prove2me | Theorems.Thm_GlobalTheory_ChartUniv_jetZero_eq
-- name    : GlobalTheory.ChartUniv.jetZero_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:10:17.61841+00:00
-- url     : https://prove2.me/theorems/baacbfd6-81d5-4d09-bdf1-b7e0147eec74
-- title:
--   Chart Univ: jet Zero eq
-- statement:
--   The Chart Univ construction uses the jet Zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L24-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]

theorem GlobalTheory.ChartUniv.jetZero_eq (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) := by sorry
