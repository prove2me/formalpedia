-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_hw_big
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_big
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:12.576571+00:00
-- url     : https://prove2.me/theorems/b9216265-2979-4dea-8c83-cc7d46540f24
-- title:
--   Minor Ordered Entries: hw big
-- statement:
--   The Minor Ordered Entries construction uses the hw big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L328-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L328-L334

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.hw_big (Q : Entries S) (hQ : Q.Good) (i : ℕ) (hi : i < Q.bigPar.length) :
    (hw Q.bigPar i : ℚ) = Q.bigPar[i] - (((Q.bigPar.length : ℚ) - 1) / 2 - i) := by sorry
