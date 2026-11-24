-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_fnVal_comp
-- name    : GlobalTheory.JetSer.fnVal_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:17.116377+00:00
-- url     : https://prove2.me/theorems/5530fcd5-3129-486b-8144-5cfdc1009fe0
-- title:
--   Jet Ser: fn Val comp
-- statement:
--   The Jet Ser construction uses the fn Val comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L41-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetSer
variable {A : Type} [CommRing A] {X : Scheme.{0}}

theorem GlobalTheory.JetSer.fnVal_comp {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by sorry
