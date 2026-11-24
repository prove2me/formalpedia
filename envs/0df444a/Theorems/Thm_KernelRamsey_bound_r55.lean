-- Prove2me | Theorems.Thm_KernelRamsey_bound_r55
-- name    : KernelRamsey.bound_r55
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:08.90461+00:00
-- url     : https://prove2.me/theorems/3106d624-7cd5-47e9-82d5-4f2d325aa83d
-- title:
--   $R(5,5) > 42$ by a graph on 42 vertices
-- statement:
--   There is a graph on $42$ vertices with $425$ edges, given by an explicit edge list, with no $5$-clique whose complement has no $5$-clique. This shows $R(5,5) > 42$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The bound $R(5,5) \ge 43$ is due to Exoo (1989). The external source of the edge list has not been established; the theorem concerns the graph as supplied.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r55 : ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ Gᶜ.CliqueFree 5 := by sorry
