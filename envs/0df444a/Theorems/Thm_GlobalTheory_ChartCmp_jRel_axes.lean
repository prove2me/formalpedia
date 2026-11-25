-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_jRel_axes
-- name    : GlobalTheory.ChartCmp.jRel_axes
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:26:55.166663+00:00
-- url     : https://prove2.me/theorems/f59a08c9-8f27-4c37-b947-dd83c516659a
-- title:
--   Chart Cmp: j Rel axes
-- statement:
--   The Chart Cmp construction uses the j Rel axes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L97-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L97-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartCmp.Axes

theorem GlobalTheory.ChartCmp.jRel_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by sorry
