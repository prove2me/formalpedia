-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch1
-- name    : IntMul.Kappa.DeferredReadout.Staircase.certificateBatch1
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:47:12.731448+00:00
-- url     : https://prove2.me/theorems/810ae26b-fc59-40f9-9e55-6a3ad682ef66
-- title:
--   Staircase witness finite nesting certificate, part 1 of 6
-- statement:
--   This is part 1 of the finite certificate for the staircase witness. Every cleared-denominator row identity numbered 0 through 600 is valid over the rationals. Every edge certificate numbered 0 through 924 accounts for every row of its earlier basis inside the later span. Every timeline numbered 0 through 294 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Staircase.certificateBatch1 :
    (∀ i, 0 ≤ i → i < 601 → validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) ∧
    (∀ i, 0 ≤ i → i < 925 → Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) ∧
    (∀ i, 0 ≤ i → i < 295 → Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) := by sorry
