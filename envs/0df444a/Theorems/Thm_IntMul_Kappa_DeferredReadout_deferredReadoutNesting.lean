-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_deferredReadoutNesting
-- name    : IntMul.Kappa.DeferredReadout.deferredReadoutNesting
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T07:54:20.952782+00:00
-- url     : https://prove2.me/theorems/7399eb26-6075-55dc-b546-3f0e3fc85eb7
-- title:
--   Checked row certificates imply nesting of all deferred readouts
-- statement:
--   Fix a block of integer row bases in $\mathbb Q^{23}$, with a chronological list of readouts for each target. Suppose its rational row identities, edge witnesses and chronological endpoint checks all pass. For any target, write $F_i$ for the rational row span used at its $i$th readout. Then
--   $$F_i\subseteq F_j\qquad(i<j).$$
--   Empty lists, singleton lists, and repeated frames are allowed. A new schedule can use this statement by supplying the three finite checks on its own data.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103 and https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L124-L146. Round seven, deferred readout nesting checks.

import Definitions.Def_IntMul_Kappa_DeferredReadoutCertificates

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.deferredReadoutNesting (d : Block) (hi : d.identitiesOK = true)
    (he : d.edgesOK = true) (ht : d.timelinesOK = true) (t : Fin d.targets.size) :
    (d.targets[t.val].map d.atEvent).Pairwise (· ≤ ·) := by sorry
