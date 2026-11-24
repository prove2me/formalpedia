-- Prove2me | Theorems.Thm_KernelRamsey_noClique_chain
-- name    : KernelRamsey.noClique_chain
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:57:51.284687+00:00
-- url     : https://prove2.me/theorems/ced09290-a8f0-4042-a958-1353c346cdd3
-- title:
--   Unrolling the clique search over the low vertices
-- statement:
--   Let `rows` encode a graph by bit masks. Suppose that for every vertex $p < n$ the search with fuel $p$ finds no clique of size $k$ among the neighbours of $p$ below $p$, that is among the candidates $(2^p - 1) \mathbin{\&} \mathrm{row}_p$. Then the search with fuel $n$ finds no clique of size $k+1$ among the $n$ lowest vertices. The search removes the highest candidate at each step, so the search over $n$ vertices unrolls into one smaller search for each vertex $p < n$. This lets a large check be split into independent pieces.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem KernelRamsey.noClique_chain (rows : List Nat) (k : Nat) :
    ∀ n : Nat, (∀ p : Nat, p < n → noClique rows p k ((2 ^ p - 1) &&& row rows p) = true) →
      noClique rows n (k + 1) (2 ^ n - 1) = true := by sorry
