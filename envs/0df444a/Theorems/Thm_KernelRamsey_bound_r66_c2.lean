-- Prove2me | Theorems.Thm_KernelRamsey_bound_r66_c2
-- name    : KernelRamsey.bound_r66_c2
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:58:03.926995+00:00
-- url     : https://prove2.me/theorems/40485a07-c33c-461d-b01e-1fdfa27ad21e
-- title:
--   Paley graph on 101 vertices, search piece C2 (vertices 20 to 29)
-- statement:
--   For the Paley graph on $\mathbb{Z}/101\mathbb{Z}$ given as bit-mask rows, and for each vertex $p$ with $20 \le p < 30$, the clique search finds no clique of size $5$ among the neighbours of $p$ below $p$ in its complement. The pieces for all $p < 101$ are combined by the unrolling theorem to show that its complement has no clique of size $6$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r66_c2 :
    ∀ p : Nat, p < 30 → 20 ≤ p →
      noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by sorry
