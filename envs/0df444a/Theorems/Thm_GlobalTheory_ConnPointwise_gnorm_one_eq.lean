-- Prove2me | Theorems.Thm_GlobalTheory_ConnPointwise_gnorm_one_eq
-- name    : GlobalTheory.ConnPointwise.gnorm_one_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:30.946478+00:00
-- url     : https://prove2.me/theorems/a737f92f-dee4-493f-85b4-4a505569f86d
-- title:
--   Conn Pointwise: gnorm one eq
-- statement:
--   The Conn Pointwise construction uses the gnorm one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L13-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.ConnPointwise
variable {g : ℕ}

theorem GlobalTheory.ConnPointwise.gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by sorry
