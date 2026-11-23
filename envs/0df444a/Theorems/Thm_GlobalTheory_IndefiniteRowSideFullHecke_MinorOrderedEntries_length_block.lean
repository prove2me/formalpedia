-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_block
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:13.070687+00:00
-- url     : https://prove2.me/theorems/28ec63c1-c635-40ff-b328-0991d8302ff1
-- title:
--   Minor Ordered Entries: length block
-- statement:
--   The Minor Ordered Entries construction uses the length block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L241-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L241-L241

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_block (x : ℚ) (n : ℕ) : (block x n).length = n := by sorry
