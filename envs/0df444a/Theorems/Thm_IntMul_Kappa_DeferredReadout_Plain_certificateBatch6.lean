-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch6
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch6
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:52:04.134209+00:00
-- url     : https://prove2.me/theorems/a7811072-b29c-4233-925c-928ac4dc7f1f
-- title:
--   Plain witness finite nesting certificate, part 6 of 6
-- statement:
--   This is part 6 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 2447 through 2936 is valid over the rationals. Every edge certificate numbered 4817 through 5780 accounts for every row of its earlier basis inside the later span. Every timeline numbered 1475 through 1770 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch6 :
    (∀ i, 2447 ≤ i → i < 2937 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 4817 ≤ i → i < 5781 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 1475 ≤ i → i < 1771 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
