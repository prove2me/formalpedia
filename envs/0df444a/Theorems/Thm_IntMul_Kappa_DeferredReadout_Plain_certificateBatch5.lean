-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch5
-- name    : IntMul.Kappa.DeferredReadout.Plain.certificateBatch5
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:51:55.173626+00:00
-- url     : https://prove2.me/theorems/06f9f315-3180-431d-b8f9-1505a2b95923
-- title:
--   Plain witness finite nesting certificate, part 5 of 6
-- statement:
--   This is part 5 of the finite certificate for the plain witness. Every cleared-denominator row identity numbered 1958 through 2446 is valid over the rationals. Every edge certificate numbered 3854 through 4816 accounts for every row of its earlier basis inside the later span. Every timeline numbered 1180 through 1474 cites the correct successive endpoints. The three numbering systems belong to the corresponding arrays in the published data. The six disjoint parts exhaust all entries and together yield the all-target nesting theorem.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.certificateBatch5 :
    (∀ i, 1958 ≤ i → i < 2447 → validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) ∧
    (∀ i, 3854 ≤ i → i < 4817 → Plain.schedule.edgeOK (Plain.schedule.edge i) = true) ∧
    (∀ i, 1180 ≤ i → i < 1475 → Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) := by sorry
