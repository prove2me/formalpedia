-- Prove2me | Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_auxiliaryReadouts
-- name    : IntMul.Kappa.DeferredReadout.Staircase.auxiliaryReadouts
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T08:11:04.681777+00:00
-- url     : https://prove2.me/theorems/cd9d7ca2-3b3f-41f4-a575-0be766bf593a
-- title:
--   Staircase witness: later deferred auxiliary edge projectors absorb earlier ones
-- statement:
--   Fix any of the 1,771 target triples of Jain's staircase witness. Every frame $U$ in its deferred readout schedule is nondegenerate for $G=I-J/9$, where $J$ is the all-ones matrix in 23 dimensions. Write $\pi_U$ for projection onto $U$ along its $G$-orthogonal complement, $t$ for the indicator of the target triple, and $P_t$ for the $G$-orthogonal projection onto its line. The associated rational auxiliary edge matrix on the 529-dimensional tensor-square space is $A_U=I-(I-\pi_U)\otimes P_t$. For every earlier and later pair in the target's chronological schedule,
--   $$A_{\mathrm{later}} A_{\mathrm{earlier}}=A_{\mathrm{earlier}}.$$
--   This covers repeated frames and applies in particular to all 18,053 adjacent transitions.
-- source:
--   https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/independent/deferred-readout/check_frames.py#L112-L148; deferred auxiliary edge in the October 20, 2026 round-seven mission discussion (comment 3c67b3da-c539-424c-a18d-e54c1884706e).

import Definitions.Def_IntMul_Kappa_DeferredReadoutProjectors
import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase

open IntMul.Kappa.DeferredReadout

theorem IntMul.Kappa.DeferredReadout.Staircase.auxiliaryReadouts (t : Fin 1771) :
    (∀ U ∈ Staircase.framesAt t, IsCompl U (gramForm.orthogonal U)) ∧
    (readoutEdges (Staircase.framesAt t) (targetDirection t)).Pairwise
      (fun earlier later => later * earlier = earlier) := by sorry
