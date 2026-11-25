-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Coord_subst_eq_X
-- name    : GlobalTheory.ChartCmp.Coord.subst_eq_X
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:06:24.993055+00:00
-- url     : https://prove2.me/theorems/a7fd439f-86a2-5770-9c59-13ceef92a7ef
-- title:
--   Coord: subst eq X
-- statement:
--   The Coord construction uses the subst eq X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsCoordinateRelationUniversalJets.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsCoordinateRelationUniversalJets.lean#L70-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V]

theorem GlobalTheory.ChartCmp.Coord.subst_eq_X {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    {φ : κ → MvPowerSeries κ' V} (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m)
    {φi : κ' → MvPowerSeries κ V} (h0i : ∀ i, MvPowerSeries.constantCoeff (φi i) = 0)
    (hφi : ∀ m, x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φi) ≫ x' m) (i : κ) :
    MvPowerSeries.subst φi (φ i) = MvPowerSeries.X i := by sorry
