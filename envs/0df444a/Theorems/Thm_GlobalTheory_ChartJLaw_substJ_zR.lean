-- Prove2me | Theorems.Thm_GlobalTheory_ChartJLaw_substJ_zR
-- name    : GlobalTheory.ChartJLaw.substJ_zR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:25.128211+00:00
-- url     : https://prove2.me/theorems/e284e406-180a-4275-9a4b-7d599a2ff2d5
-- title:
--   Chart JLaw: subst J z R
-- statement:
--   The Chart JLaw construction uses the subst J z R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsFormalGroupLawOfChartOfJetChart.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsFormalGroupLawOfChartOfJetChart.lean#L39-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}

theorem GlobalTheory.ChartJLaw.substJ_zR {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (q : Fin 1 × Fin d) : substJ m φ hφ (zR m q) = JetSer.toJet m (φ q.2) := by sorry
