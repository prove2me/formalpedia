-- Prove2me | Theorems.Thm_GlobalTheory_NormRos_isNormRos_unique
-- name    : GlobalTheory.NormRos.isNormRos_unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:37:18.629009+00:00
-- url     : https://prove2.me/theorems/1689c077-c4e5-4941-bb9b-ac70a935ab29
-- title:
--   Norm Ros: is Norm Ros unique
-- statement:
--   The Norm Ros construction uses the is Norm Ros unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGenRosati.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGenRosati.lean#L106-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NormRos
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
omit [IsCommMonObj G]

theorem GlobalTheory.NormRos.isNormRos_unique {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (hs : Function.Surjective (G ⊗ G).hom.appTop.hom) {u u' : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)}
    (h : IsNormRos L f g u) (h' : IsNormRos L f g u') : u.s = u'.s := by sorry
