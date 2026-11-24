-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_small
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:10.846259+00:00
-- url     : https://prove2.me/theorems/b199cc83-42ce-497d-b213-8b8058b9b052
-- title:
--   Minor Ordered Entries: length small
-- statement:
--   The Minor Ordered Entries construction uses the length small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L260-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L260-L263

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_small (Q : Entries S) : Q.smallPar.length = S.nC S.m := by sorry
