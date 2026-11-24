-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_jetHom_toJet
-- name    : GlobalTheory.JetSer.jetHom_toJet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:21.510017+00:00
-- url     : https://prove2.me/theorems/c5245611-16e8-4f34-aa10-0e2f44f3a7be
-- title:
--   Jet Ser: jet Hom to Jet
-- statement:
--   The Jet Ser construction uses the jet Hom to Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L79-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L79-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]

theorem GlobalTheory.JetSer.jetHom_toJet {σ : Type} [Finite σ] (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
    (ψ : JetR R σ m →ₐ[R] JetR R κ m) (hψ : ∀ j, ψ (zR m j) = toJet m (a j)) (g : MvPowerSeries σ R) :
    ψ (toJet m g) = toJet m (subst a g) := by sorry
