-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_jetTruncR_toJet
-- name    : GlobalTheory.JetSer.jetTruncR_toJet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:44:08.963931+00:00
-- url     : https://prove2.me/theorems/c0fa2c99-ef58-4b81-9a6d-0e97d3c07c9e
-- title:
--   Jet Ser: jet Trunc R to Jet
-- statement:
--   The Jet Ser construction uses the jet Trunc R to Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L43-L47

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

theorem GlobalTheory.JetSer.jetTruncR_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetTruncR R κ m (toJet (m + 1) g) = toJet m g := by sorry
