-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_JCalc_jeq_map
-- name    : GlobalTheory.ChartCmp.JCalc.jeq_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:09:15.540555+00:00
-- url     : https://prove2.me/theorems/afaa2d6a-479d-460e-8ce7-8c066e8137fb
-- title:
--   JCalc: jeq map
-- statement:
--   The JCalc construction uses the jeq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesJetEqCalculus.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesJetEqCalculus.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.JCalc
variable {R : Type} [CommRing R] {σ : Type} {m : ℕ}

theorem GlobalTheory.ChartCmp.JCalc.jeq_map {R' : Type} [CommRing R'] (β : R →+* R') {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) := by sorry
