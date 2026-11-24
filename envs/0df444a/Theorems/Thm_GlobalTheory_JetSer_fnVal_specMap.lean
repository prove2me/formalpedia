-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_fnVal_specMap
-- name    : GlobalTheory.JetSer.fnVal_specMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.457303+00:00
-- url     : https://prove2.me/theorems/9da8e142-6754-4897-a132-869a7d1e944f
-- title:
--   Jet Ser: fn Val spec Map
-- statement:
--   The Jet Ser construction uses the fn Val spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L27-L39

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

theorem GlobalTheory.JetSer.fnVal_specMap {B : Type} [CommRing B] (ψ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal (Spec.map (CommRingCat.ofHom ψ) ≫ p) U f = ψ (fnVal p U f) := by sorry
