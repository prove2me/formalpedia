-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_coord_dir
-- name    : GlobalTheory.ChartCmp.CoordDir.coord_dir
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:29.706136+00:00
-- url     : https://prove2.me/theorems/c009a75f-7cd8-4673-aa03-584f753a221c
-- title:
--   Coord Dir: coord dir
-- statement:
--   The Coord Dir construction uses the coord dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TangentDirectionTwoChartsLinearPart.lean#L151-L158

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

theorem GlobalTheory.ChartCmp.CoordDir.coord_dir : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by sorry
