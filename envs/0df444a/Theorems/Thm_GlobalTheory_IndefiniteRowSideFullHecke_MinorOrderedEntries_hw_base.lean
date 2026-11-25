-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_base
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_base
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:57.426642+00:00
-- url     : https://prove2.me/theorems/84d7cb28-4c1d-4609-b1ea-863385d725e5
-- title:
--   Minor Ordered Entries: hw base
-- statement:
--   The Minor Ordered Entries construction uses the hw base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L336-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L336-L338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped TensorProduct Kronecker
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Sizes} (P : ι → Entries S)

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_base (Q : Entries S) (i : ℕ) (hi : i < Q.basePar.length) :
    (hw Q.basePar i : ℚ) = Q.basePar[i] - (((Q.basePar.length : ℚ) - 1) / 2 - i) := by sorry
