-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_BilAdd_hasSubst_pts
-- name    : GlobalTheory.ChartCmp.BilAdd.hasSubst_pts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:24:28.946302+00:00
-- url     : https://prove2.me/theorems/6d289a94-1d7f-5940-874e-242c5154df02
-- title:
--   Bil Add: has Subst pts
-- statement:
--   The Bil Add construction uses the has Subst pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetEqBilinearSeriesOfBiadditive.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.BilAdd
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.ChartCmp.BilAdd.hasSubst_pts {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin l × Fin d => a p.1 p.2) := by sorry
