-- Prove2me | Theorems.Thm_GlobalTheory_PushChart_isCombAtG_comp
-- name    : GlobalTheory.PushChart.isCombAtG_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:03:39.414956+00:00
-- url     : https://prove2.me/theorems/ef0c1181-d69a-49e0-8be5-e510c6d7e72d
-- title:
--   Push Chart: is Comb At G comp
-- statement:
--   The Push Chart construction uses the is Comb At G comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L21-L30

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

theorem GlobalTheory.PushChart.isCombAtG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t t' : SAB H X0}
    (ψ : t.G ⟶ t'.G) [IsMonHom ψ] {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {v' : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v' i = v i ≫ ψ.left) {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t' x0 v' cf (w ≫ ψ.left) := by sorry
