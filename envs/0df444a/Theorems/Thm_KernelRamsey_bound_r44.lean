-- Prove2me | Theorems.Thm_KernelRamsey_bound_r44
-- name    : KernelRamsey.bound_r44
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:05.241869+00:00
-- url     : https://prove2.me/theorems/8b51a05a-dfb1-457c-a064-cd4376c51df2
-- title:
--   $R(4,4) > 17$ by the Paley graph on 17 vertices
-- statement:
--   There is a graph on $17$ vertices with no $4$-clique whose complement has no $4$-clique, namely the Paley graph on $\mathbb{Z}/17\mathbb{Z}$ in which $i$ and $j$ are adjacent when $j-i$ is a non-zero square modulo $17$. This shows $R(4,4) > 17$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(4,4)=18$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r44 : ∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4 := by sorry
