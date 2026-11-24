-- Prove2me | Theorems.Thm_KernelRamsey_ramsey_avoidance
-- name    : KernelRamsey.ramsey_avoidance
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:42:51.714892+00:00
-- url     : https://prove2.me/theorems/4adf91e2-bb6d-42f0-8070-a39e0bdb0a1b
-- title:
--   Two successful clique searches give a Ramsey avoidance graph
-- statement:
--   Let `rows` encode a graph on $n$ vertices by bit masks, and suppose the rows are symmetric. If the clique search finds no $s$-clique in the graph and no $t$-clique in its complement rows, then there exists a simple graph $G$ on $\{0,\dots,n-1\}$ with no $s$-clique whose complement has no $t$-clique. Since an independent set of $G$ is a clique of the complement, $G$ witnesses the Ramsey lower bound $R(s,t) > n$. The graph $G$ has an edge between $i \neq j$ when bit $j$ of row $i$ is set.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem KernelRamsey.ramsey_avoidance {n s t : Nat} (rows : List Nat)
    (hsymm : ∀ i j : Fin n, (row rows i.val).testBit j.val = (row rows j.val).testBit i.val)
    (h1 : noClique rows n s (fullMask n) = true)
    (h2 : noClique (complementRows n rows) n t (fullMask n) = true) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree s ∧ Gᶜ.CliqueFree t := by sorry
