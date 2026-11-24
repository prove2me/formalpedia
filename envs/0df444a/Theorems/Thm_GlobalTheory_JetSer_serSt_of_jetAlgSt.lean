-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_serSt_of_jetAlgSt
-- name    : GlobalTheory.JetSer.serSt_of_jetAlgSt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:42:11.624982+00:00
-- url     : https://prove2.me/theorems/faf38e13-938e-4c97-b310-05664ef2f4f1
-- title:
--   Jet Ser: ser St of jet Alg St
-- statement:
--   The Jet Ser construction uses the ser St of jet Alg St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L114-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsNilpotentOfMemKerJetTruncR.lean#L114-L154

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

theorem GlobalTheory.JetSer.serSt_of_jetAlgSt : JetAlgSt → SerSt := by sorry
