-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordLaw_eq_comp1_inv
-- name    : GlobalTheory.ChartCmp.CoordLaw.eq_comp1_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:23.566461+00:00
-- url     : https://prove2.me/theorems/d36d8725-4703-5f33-a876-77ac12106624
-- title:
--   Coord Law: eq comp1 inv
-- statement:
--   The Coord Law construction uses the eq comp1 inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L48-L50

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

theorem GlobalTheory.ChartCmp.CoordLaw.eq_comp1_inv {n : ℕ} {φ φi : Pt V 1 d} (h : IsInvPair φ φi) {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : comp1 φ a = b) : a = comp1 φi b := by sorry
