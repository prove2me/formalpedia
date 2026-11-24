-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_jet
-- name    : GlobalTheory.JetSer.top_le_preimage_jet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:41:21.436337+00:00
-- url     : https://prove2.me/theorems/0d2c55f8-414e-48f2-a36c-67e9d1c92ff6
-- title:
--   Jet Ser: top le preimage jet
-- statement:
--   The Jet Ser construction uses the top le preimage jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L102-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L102-L110

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
variable {R : Type} [CommRing R] {κ : Type}

theorem GlobalTheory.JetSer.top_le_preimage_jet {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by sorry
