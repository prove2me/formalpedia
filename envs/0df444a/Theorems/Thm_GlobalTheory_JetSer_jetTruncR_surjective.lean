-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_jetTruncR_surjective
-- name    : GlobalTheory.JetSer.jetTruncR_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:39.817215+00:00
-- url     : https://prove2.me/theorems/c7441901-7d29-4144-8dfb-90a5e40ea04d
-- title:
--   Jet Ser: jet Trunc R surjective
-- statement:
--   The Jet Ser construction uses the jet Trunc R surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L86-L89

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

theorem GlobalTheory.JetSer.jetTruncR_surjective (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by sorry
