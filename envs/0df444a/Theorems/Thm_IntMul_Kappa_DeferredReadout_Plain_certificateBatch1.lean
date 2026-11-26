-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch1
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch1
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:47:10.737665+00:00
-- url     : https://prove2.me/theorems/41acecaf-3436-41a5-af93-7561ebb5377a
-- title:
--   Plain witness finite nesting certificate, part 1 of 6
-- statement:
--   This is part 1 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 0 through 488 is valid over the rationals. Every edge certificate numbered 0 through 962 accounts for every row of its earlier basis inside the later span. Every timeline numbered 0 through 294 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch1 :
    (∀ i, 0 ≤ i → i < 489 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 0 ≤ i → i < 963 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 0 ≤ i → i < 295 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
