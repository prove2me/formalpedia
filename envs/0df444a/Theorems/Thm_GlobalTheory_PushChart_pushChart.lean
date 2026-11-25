-- Prove2me | Theorems.Thm_GlobalTheory_PushChart_pushChart
-- name    : GlobalTheory.PushChart.pushChart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:50:11.868164+00:00
-- url     : https://prove2.me/theorems/75df017d-d0ed-5a99-b9c5-1d61ccf6f281
-- title:
--   Push Chart: push Chart
-- statement:
--   The Push Chart construction uses the push Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L48-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart
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
open GlobalTheory GlobalTheory.PushChart

theorem GlobalTheory.PushChart.pushChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), ∃ x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G, (∀ m, (x' m).left = (x m).left ≫ n.φ) ∧ (GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x') ∧ (∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V), IsChartG t (𝟙 (Sp V)) d F act tg uv x → IsChartG t' (𝟙 (Sp V)) d F act (fun l => tg l ≫ n.φ) uv x') ∧ ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u (v ≫ n.φ) := by sorry
