-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_law_act_of_coordRel
-- name    : GlobalTheory.ChartCmp.law_act_of_coordRel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:55.154802+00:00
-- url     : https://prove2.me/theorems/dd9e30c8-05bb-4556-b690-4e56bcef515d
-- title:
--   Chart Cmp: law act of coord Rel
-- statement:
--   The Chart Cmp construction uses the law act of coord Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L121-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRel.lean#L121-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
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
open GlobalTheory.ChartCmp.CoordLaw

theorem GlobalTheory.ChartCmp.law_act_of_coordRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ φi : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) ∧ ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ) := by sorry
