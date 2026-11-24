-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_eval_standard_points_three
-- name    : GlobalTheory.ChartBaseChange.eval_standard_points_three
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:00.645528+00:00
-- url     : https://prove2.me/theorems/dd4012e5-1c90-46a2-bd2e-42e08bbf1c10
-- title:
--   Chart Base Change: eval standard points three
-- statement:
--   The Chart Base Change construction uses the eval standard points three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L302-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L302-L307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {d n N : ℕ}

theorem GlobalTheory.ChartBaseChange.eval_standard_points_three (f : PS R 3 d) :
    ev (n := 3) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 2] f = f := by sorry
