-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_tanPt_inj
-- name    : GlobalTheory.ChartCmp.CoordDir.tanPt_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:09:51.967644+00:00
-- url     : https://prove2.me/theorems/a5975a20-f4c6-544d-b1be-e0815b02ba63
-- title:
--   Coord Dir: tan Pt inj
-- statement:
--   The Coord Dir construction uses the tan Pt inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L135-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L135-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
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
variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}

theorem GlobalTheory.ChartCmp.CoordDir.tanPt_inj {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} (hx : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x)
    {g g' : Fin 1 × Fin d → V} (h : tanPt x g = tanPt x g') : g = g' := by sorry
