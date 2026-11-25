-- Prove2me | Theorems.Thm_GlobalTheory_BddArc_AbsSumAt_const
-- name    : GlobalTheory.BddArc.AbsSumAt.const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:18.995524+00:00
-- url     : https://prove2.me/theorems/1f69d45f-1221-4d07-b718-8dfa17cb9f1a
-- title:
--   Abs Sum At: const
-- statement:
--   The Abs Sum At construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EvalTwistTxEqZeroOfAevalArcTx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.BddArc
variable {C : Type} [NontriviallyNormedField C] [CompleteSpace C]
omit [CompleteSpace C]

theorem GlobalTheory.BddArc.AbsSumAt.const (u a : C) : AbsSumAt u (PowerSeries.C a) a := by sorry
