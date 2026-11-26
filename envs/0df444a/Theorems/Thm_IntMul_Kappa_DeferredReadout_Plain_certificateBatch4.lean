-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch4
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch4
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:51:51.190066+00:00
-- url     : https://prove2.me/theorems/a7441cc5-4cbc-49f3-900d-bf1f8ce98f04
-- title:
--   Plain witness finite nesting certificate, part 4 of 6
-- statement:
--   This is part 4 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 1468 through 1957 is valid over the rationals. Every edge certificate numbered 2890 through 3853 accounts for every row of its earlier basis inside the later span. Every timeline numbered 885 through 1179 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch4 :
    (∀ i, 1468 ≤ i → i < 1958 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 2890 ≤ i → i < 3854 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 885 ≤ i → i < 1180 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
