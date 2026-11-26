-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch3
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch3
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:51:42.791804+00:00
-- url     : https://prove2.me/theorems/4a70dbf8-e2ec-536c-b2ea-3c92bf7f6a1f
-- title:
--   Plain witness finite nesting certificate, part 3 of 6
-- statement:
--   This is part 3 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 979 through 1467 is valid over the rationals. Every edge certificate numbered 1927 through 2889 accounts for every row of its earlier basis inside the later span. Every timeline numbered 590 through 884 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch3 :
    (∀ i, 979 ≤ i → i < 1468 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 1927 ≤ i → i < 2890 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 590 ≤ i → i < 885 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
