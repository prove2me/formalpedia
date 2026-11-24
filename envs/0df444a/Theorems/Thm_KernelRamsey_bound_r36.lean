-- Prove2me | Theorems.Thm_KernelRamsey_bound_r36
-- name    : KernelRamsey.bound_r36
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:01.576411+00:00
-- url     : https://prove2.me/theorems/a35c927d-6178-4b9d-8bab-86da42abdf8a
-- title:
--   $R(3,6) > 17$ by a graph on 17 vertices
-- statement:
--   There is a graph on $17$ vertices, given by an explicit edge list, with no triangle whose complement has no $6$-clique. This shows $R(3,6) > 17$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(3,6)=18$. The external source of the edge list has not been established; the theorem concerns the graph as supplied.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r36 : ∃ G : SimpleGraph (Fin 17), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 6 := by sorry
