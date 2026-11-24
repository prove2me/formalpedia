-- Prove2me | Theorems.Thm_KernelRamsey_bound_r66
-- name    : KernelRamsey.bound_r66
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:03.863914+00:00
-- url     : https://prove2.me/theorems/1c90e7a3-8c84-4574-bdaa-3b703426a927
-- title:
--   $R(6,6) > 101$ by the Paley graph on 101 vertices
-- statement:
--   There is a graph on $101$ vertices with $2525$ edges with no $6$-clique whose complement has no $6$-clique, namely the Paley graph on $\mathbb{Z}/101\mathbb{Z}$ in which $i$ and $j$ are adjacent when $j-i$ is a non-zero square modulo $101$. This shows $R(6,6) > 101$. The theorem is proved by evaluating two bit-mask clique searches and a symmetry check with the Lean kernel, without symmetry reduction.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem KernelRamsey.bound_r66 : ∃ G : SimpleGraph (Fin 101), G.CliqueFree 6 ∧ Gᶜ.CliqueFree 6 := by sorry
