-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch2
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch2
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:51:25.715963+00:00
-- url     : https://prove2.me/theorems/91726ccb-af70-56b4-a353-3b281f242596
-- title:
--   Plain witness finite nesting certificate, part 2 of 6
-- statement:
--   This is part 2 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 489 through 978 is valid over the rationals. Every edge certificate numbered 963 through 1926 accounts for every row of its earlier basis inside the later span. Every timeline numbered 295 through 589 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch2 :
    (∀ i, 489 ≤ i → i < 979 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 963 ≤ i → i < 1927 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 295 ≤ i → i < 590 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
