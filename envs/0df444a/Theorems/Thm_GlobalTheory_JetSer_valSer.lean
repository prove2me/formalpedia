-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_valSer
-- name    : GlobalTheory.JetSer.valSer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:42:00.224223+00:00
-- url     : https://prove2.me/theorems/b78798d1-9051-47cd-8fbb-9fb9dbaa0b23
-- title:
--   Jet Ser: val Ser
-- statement:
--   The Jet Ser construction uses the val Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ValSerGermFnVal.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ValSerGermFnVal.lean#L21-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.valSer : ValSerSt := by sorry
