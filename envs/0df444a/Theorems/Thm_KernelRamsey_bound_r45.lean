-- Prove2me | Theorems.Thm_KernelRamsey_bound_r45
-- name    : KernelRamsey.bound_r45
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:02.533511+00:00
-- url     : https://prove2.me/theorems/00771df3-51ea-45db-8c54-e7d399c92864
-- title:
--   $R(4,5) > 24$ by a graph on 24 vertices
-- statement:
--   There is a graph on $24$ vertices, given by an explicit edge list, with no $4$-clique whose complement has no $5$-clique. This shows $R(4,5) > 24$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(4,5)=25$. The external source of the edge list has not been established; the theorem concerns the graph as supplied.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r45 : ∃ G : SimpleGraph (Fin 24), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 5 := by sorry
