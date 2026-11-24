-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_fnVal_res
-- name    : GlobalTheory.JetSer.fnVal_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:48.452053+00:00
-- url     : https://prove2.me/theorems/5e0cc854-9d8b-4b36-a311-0ddec6329714
-- title:
--   Jet Ser: fn Val res
-- statement:
--   The Jet Ser construction uses the fn Val res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L53-L61

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

theorem GlobalTheory.JetSer.fnVal_res (p : Spec (CommRingCat.of A) ⟶ X) (U V : X.Opens) (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)) :
    ⊤ ≤ p ⁻¹ᵁ V ∧ fnVal p V f = fnVal p U ((X.presheaf.map (homOfLE hUV).op).hom f) := by sorry
