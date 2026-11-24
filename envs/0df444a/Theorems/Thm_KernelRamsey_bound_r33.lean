-- Prove2me | Theorems.Thm_KernelRamsey_bound_r33
-- name    : KernelRamsey.bound_r33
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:01.641725+00:00
-- url     : https://prove2.me/theorems/f34fb9dd-ba6f-4eaf-b690-872d16b69aa3
-- title:
--   $R(3,3) > 5$ by the 5-cycle
-- statement:
--   There is a graph on $5$ vertices with no triangle whose complement has no triangle, namely the 5-cycle. This shows $R(3,3) > 5$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(3,3)=6$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r33 : ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by sorry
