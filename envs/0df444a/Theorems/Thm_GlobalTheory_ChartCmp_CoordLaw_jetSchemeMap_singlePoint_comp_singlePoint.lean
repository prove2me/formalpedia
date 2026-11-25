-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_jetSchemeMap_singlePoint_comp_singlePoint
-- name    : GlobalTheory.ChartCmp.CoordLaw.jetSchemeMap_singlePoint_comp_singlePoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:59.397846+00:00
-- url     : https://prove2.me/theorems/a7f9ee1d-8bcd-5722-9831-6c65a36af324
-- title:
--   Coord Law: jet Scheme Map single Point comp single Point
-- statement:
--   The Coord Law construction uses the jet Scheme Map single Point comp single Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L76-L83

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

theorem GlobalTheory.ChartCmp.CoordLaw.jetSchemeMap_singlePoint_comp_singlePoint (m : ℕ) {n : ℕ} (a : Pt V n d) (φ : Pt V 1 d)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    sub1 m a ≫ sub1 m φ = sub1 m (comp1 φ a) := by sorry
