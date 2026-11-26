-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_nesting
-- name    : IntMul.Kappa.DeferredReadout.Staircase.nesting
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:09:07.205011+00:00
-- url     : https://prove2.me/theorems/f478b1e5-f8ff-5a57-aee5-e5da3fe554c8
-- title:
--   Staircase round-seven witness: every earlier deferred frame lies in every later frame
-- statement:
--   Fix any of the 1,771 target triples in the staircase witness to Jain's round-seven bit network. Read its deferred slots in their published time order. If $F_i$ is the rational row span in $\mathbb Q^{23}$ of the frame at slot position $i$, then
--   $$F_i\subseteq F_j\qquad(i<j).$$
--   All 19,822 readouts are represented across the target triples. This establishes the nesting portion of the frame check for this particular schedule.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Staircase.nesting (t : Fin 1771) : (Staircase.framesAt t).Pairwise (· ≤ ·) := by sorry
