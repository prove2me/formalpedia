-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_PushAd_subst_act
-- name    : GlobalTheory.ChartCmp.PushAd.subst_act
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:23.466557+00:00
-- url     : https://prove2.me/theorems/f6ad8eaf-a123-5f85-9ce8-0f2ea7e6ae13
-- title:
--   Push Ad: subst act
-- statement:
--   The Push Ad construction uses the subst act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L107-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AdjointnessSeriesTransportFrames.lean#L107-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem GlobalTheory.ChartCmp.PushAd.subst_act (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
    {n n' : ℕ} (m : ℕ) (f : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (α : t.G ⟶ t.G)
    (hα : x m ≫ α = Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)) ≫ x m)
    (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = psIn d m ![k] (f j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k ≫ α := by sorry
