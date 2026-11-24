-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_of_nil
-- name    : GlobalTheory.JetSer.top_le_preimage_of_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:33.426893+00:00
-- url     : https://prove2.me/theorems/11134b61-469d-4b8d-81ce-9db924e7c058
-- title:
--   Jet Ser: top le preimage of nil
-- statement:
--   The Jet Ser construction uses the top le preimage of nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L63-L79

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

theorem GlobalTheory.JetSer.top_le_preimage_of_nil {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by sorry
