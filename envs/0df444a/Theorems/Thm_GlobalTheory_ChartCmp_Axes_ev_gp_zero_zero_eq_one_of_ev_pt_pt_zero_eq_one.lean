-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Axes_ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one
-- name    : GlobalTheory.ChartCmp.Axes.ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:27:57.112186+00:00
-- url     : https://prove2.me/theorems/b1ec99ad-aecd-573d-96e6-684efcf84290
-- title:
--   Axes: ev gp zero zero eq one of ev pt pt zero eq one
-- statement:
--   The Axes construction uses the ev gp zero zero eq one of ev pt pt zero eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L85-L91

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

theorem GlobalTheory.ChartCmp.Axes.ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![z, 0, 0] f = 1 := by sorry
