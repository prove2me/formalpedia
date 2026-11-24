-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_toJetHom_apply
-- name    : GlobalTheory.JetSer.toJetHom_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:52.70595+00:00
-- url     : https://prove2.me/theorems/2483da5e-c1c4-4ad8-a56e-1d24ddfd89c5
-- title:
--   Jet Ser: to Jet Hom apply
-- statement:
--   The Jet Ser construction uses the to Jet Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L41-L41

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

theorem GlobalTheory.JetSer.toJetHom_apply (m : ℕ) (g : MvPowerSeries κ R) : toJetHom R κ m g = toJet m g := by sorry
