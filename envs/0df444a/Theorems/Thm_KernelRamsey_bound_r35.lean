-- Prove2me | Theorems.Thm_KernelRamsey_bound_r35
-- name    : KernelRamsey.bound_r35
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:01.480719+00:00
-- url     : https://prove2.me/theorems/b1e32f6d-1a71-4eae-a88f-d79614db6959
-- title:
--   $R(3,5) > 13$ by a circulant graph on 13 vertices
-- statement:
--   There is a graph on $13$ vertices with no triangle whose complement has no $5$-clique, namely the circulant graph on $\mathbb{Z}/13\mathbb{Z}$ with differences $\{1,5,8,12\}$. This shows $R(3,5) > 13$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel. The classical value is $R(3,5)=14$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r35 : ∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5 := by sorry
