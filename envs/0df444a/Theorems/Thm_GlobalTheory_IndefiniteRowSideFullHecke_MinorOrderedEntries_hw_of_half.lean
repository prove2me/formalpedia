-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_of_half
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_of_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:19.962958+00:00
-- url     : https://prove2.me/theorems/5cc49e06-f126-4af1-a58b-8500287105fc
-- title:
--   Minor Ordered Entries: hw of half
-- statement:
--   The Minor Ordered Entries construction uses the hw of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L284-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L284-L289

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_of_half (p : List ℚ) (hl : Even p.length) (h : ∀ x ∈ p, ∃ z : ℤ, x = z + 1 / 2) (i : ℕ) (hi : i < p.length) :
    (hw p i : ℚ) = p[i] - (((p.length : ℚ) - 1) / 2 - i) := by sorry
