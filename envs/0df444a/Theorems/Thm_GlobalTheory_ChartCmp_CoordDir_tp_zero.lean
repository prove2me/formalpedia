-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_tp_zero
-- name    : GlobalTheory.ChartCmp.CoordDir.tp_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:23.337838+00:00
-- url     : https://prove2.me/theorems/b3292c21-5706-44a0-aa45-263374b6725e
-- title:
--   Coord Dir: tp zero
-- statement:
--   The Coord Dir construction uses the tp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L26-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordDir
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}

theorem GlobalTheory.ChartCmp.CoordDir.tp_zero : (tp (0 : Fin 1 × Fin d → V)) =
      (Algebra.ofId V (DualNumber V)).comp (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by sorry
