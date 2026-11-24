-- Prove2me | Theorems.Thm_KernelRamsey_bound_r34
-- name    : KernelRamsey.bound_r34
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:00.42257+00:00
-- url     : https://prove2.me/theorems/d3f2a0d3-ab5c-4c30-9599-2c903cbe2b40
-- title:
--   $R(3,4) > 8$ by the Möbius ladder on 8 vertices
-- statement:
--   There is a graph on $8$ vertices with no triangle whose complement has no $4$-clique, namely the Möbius ladder (an $8$-cycle with the four antipodal chords). This shows $R(3,4) > 8$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(3,4)=9$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r34 : ∃ G : SimpleGraph (Fin 8), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4 := by sorry
