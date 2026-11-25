-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Axes_ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one
-- name    : GlobalTheory.ChartCmp.Axes.ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:23:59.434802+00:00
-- url     : https://prove2.me/theorems/850e4776-3ef6-4ca0-b29a-a9be9e91dbb6
-- title:
--   Axes: ev zero zero gp eq one of ev zero pt pt eq one
-- statement:
--   The Axes construction uses the ev zero zero gp eq one of ev zero pt pt eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L77-L83

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Axes
variable {R : Type} [CommRing R]

theorem GlobalTheory.ChartCmp.Axes.ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![0, 0, z] f = 1 := by sorry
