-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_nesting
-- name    : IntMul.Kappa.DeferredReadout.Plain.nesting
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T08:08:59.837797+00:00
-- url     : https://prove2.me/theorems/782aeb6b-af3e-58e5-b226-13299a5af589
-- title:
--   Plain round-seven witness: every earlier deferred frame lies in every later frame
-- statement:
--   Fix any of the 1,771 target triples in the plain witness to Jain's round-seven bit network. Read its deferred slots in their published time order. If $F_i$ is the rational row span in $\mathbb Q^{23}$ of the frame at slot position $i$, then
--   $$F_i\subseteq F_j\qquad(i<j).$$
--   All 15,949 readouts are represented across the target triples. This establishes the nesting portion of the frame check for this particular schedule.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/joint-frame-stack/check_design.py#L78-L103

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Plain.nesting (t : Fin 1771) : (Plain.framesAt t).Pairwise (· ≤ ·) := by sorry
