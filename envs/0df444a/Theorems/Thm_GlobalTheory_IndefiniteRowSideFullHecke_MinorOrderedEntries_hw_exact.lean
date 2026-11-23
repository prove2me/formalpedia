-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_exact
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:24.826606+00:00
-- url     : https://prove2.me/theorems/3f0a60f2-cc93-45ae-b878-9de900f95030
-- title:
--   Minor Ordered Entries: hw exact
-- statement:
--   The Minor Ordered Entries construction uses the hw exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L265-L270

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_exact (p : List ℚ) (h : ∀ x ∈ p, ∃ z : ℤ, x = z + ((p.length : ℚ) - 1) / 2) (i : ℕ) (hi : i < p.length) :
    (hw p i : ℚ) = p[i] - (((p.length : ℚ) - 1) / 2 - i) := by sorry
