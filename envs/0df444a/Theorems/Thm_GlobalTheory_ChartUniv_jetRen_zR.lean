-- Prove2me | Theorems.Thm_GlobalTheory_ChartUniv_jetRen_zR
-- name    : GlobalTheory.ChartUniv.jetRen_zR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:22.805799+00:00
-- url     : https://prove2.me/theorems/75735e54-6b1f-479c-a84c-b5d78ddb90cd
-- title:
--   Chart Univ: jet Ren z R
-- statement:
--   The Chart Univ construction uses the jet Ren z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L46-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
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

theorem GlobalTheory.ChartUniv.jetRen_zR {κ κ' : Type} (f : κ → κ') (m : ℕ) (j : κ) : jetRen (R := R) f m (zR m j) = zR m (f j) := by sorry
