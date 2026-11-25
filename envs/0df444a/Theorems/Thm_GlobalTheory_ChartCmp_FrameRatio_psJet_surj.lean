-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_FrameRatio_psJet_surj
-- name    : GlobalTheory.ChartCmp.FrameRatio.psJet_surj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:14:43.413706+00:00
-- url     : https://prove2.me/theorems/73584a64-a1f8-4ed3-a8ca-38597a04ac85
-- title:
--   Frame Ratio: ps Jet surj
-- statement:
--   The Frame Ratio construction uses the ps Jet surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetFramesDifferByUnitEachOrder.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetFramesDifferByUnitEachOrder.lean#L44-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
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
open Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.FrameRatio

theorem GlobalTheory.ChartCmp.FrameRatio.psJet_surj {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (m : ℕ) (a : Jet R κ m) :
    ∃ f : MvPowerSeries κ R, psJet m f = a := by sorry
