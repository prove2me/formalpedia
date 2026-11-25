-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_jetSchemeMap_pointFamily_comp_singlePoint
-- name    : GlobalTheory.ChartCmp.CoordLaw.jetSchemeMap_pointFamily_comp_singlePoint
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:09:41.142377+00:00
-- url     : https://prove2.me/theorems/9fc1240f-4688-57f5-93e5-d72be3decdff
-- title:
--   Coord Law: jet Scheme Map point Family comp single Point
-- statement:
--   The Coord Law construction uses the jet Scheme Map point Family comp single Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L71-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}

theorem GlobalTheory.ChartCmp.CoordLaw.jetSchemeMap_pointFamily_comp_singlePoint (m : ℕ) {k n : ℕ} (a : Fin k → Pt V n d) (b : Pt V k d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    sub m a ≫ sub1 m b = sub1 m (fun i => ev a (b i)) := by sorry
