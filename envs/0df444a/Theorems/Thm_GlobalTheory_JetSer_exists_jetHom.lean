-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_jetHom
-- name    : GlobalTheory.JetSer.exists_jetHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:19.657871+00:00
-- url     : https://prove2.me/theorems/427ab701-f40a-4c8c-8157-75897165668e
-- title:
--   Jet Ser: exists jet Hom
-- statement:
--   The Jet Ser construction uses the exists jet Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L74-L77

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

theorem GlobalTheory.JetSer.exists_jetHom {σ : Type} (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ) :
    ∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j) := by sorry
