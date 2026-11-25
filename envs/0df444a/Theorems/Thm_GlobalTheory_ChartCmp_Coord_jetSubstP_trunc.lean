-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Coord_jetSubstP_trunc
-- name    : GlobalTheory.ChartCmp.Coord.jetSubstP_trunc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:08:58.210504+00:00
-- url     : https://prove2.me/theorems/ed5d0d9b-0921-4037-90c9-db029f0c7514
-- title:
--   Coord: jet Subst P trunc
-- statement:
--   The Coord construction uses the jet Subst P trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsCoordinateRelationUniversalJets.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsCoordinateRelationUniversalJets.lean#L29-L30

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

theorem GlobalTheory.ChartCmp.Coord.jetSubstP_trunc {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (φ : κ → MvPowerSeries κ' V) :
    jetSubstP m (fun p => psTrunc m (φ p)) = jetSubstPS (m := m) φ := by sorry
