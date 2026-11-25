-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Axes_jEq_ev
-- name    : GlobalTheory.ChartCmp.Axes.jEq_ev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:24:07.733688+00:00
-- url     : https://prove2.me/theorems/7e7e9ff6-9212-4252-9b86-0e19858bb7d1
-- title:
--   Axes: j Eq ev
-- statement:
--   The Axes construction uses the j Eq ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean#L35-L53

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

theorem GlobalTheory.ChartCmp.Axes.jEq_ev {d n n' m : ℕ} (a : Fin n → Pt R n' d) (ha : ∀ j, GP (a j)) {f g : PS R n d} (h : JEq m f g) :
    JEq m (ev a f) (ev a g) := by sorry
