-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_MinorOrderedEntries_length_big
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_big
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:15.350107+00:00
-- url     : https://prove2.me/theorems/f0354fbb-d5e2-46fd-8660-ee954831b0c6
-- title:
--   Minor Ordered Entries: length big
-- statement:
--   The Minor Ordered Entries construction uses the length big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L250-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean#L250-L253

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.length_big (Q : Entries S) : Q.bigPar.length = S.nR S.m := by sorry
