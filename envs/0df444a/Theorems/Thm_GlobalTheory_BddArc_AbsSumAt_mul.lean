-- Prove2me | Theorems.Thm_GlobalTheory_BddArc_AbsSumAt_mul
-- name    : GlobalTheory.BddArc.AbsSumAt.mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:59.521462+00:00
-- url     : https://prove2.me/theorems/42d15d72-1533-4c63-a501-6ee05bbd54c9
-- title:
--   Abs Sum At: mul
-- statement:
--   The Abs Sum At construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EvalTwistTxEqZeroOfAevalArcTx.lean#L33-L46

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

theorem GlobalTheory.BddArc.AbsSumAt.mul {u : C} {f g : PowerSeries C} {a b : C} (hf : AbsSumAt u f a) (hg : AbsSumAt u g b) :
    AbsSumAt u (f * g) (a * b) := by sorry
