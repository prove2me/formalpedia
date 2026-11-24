-- Prove2me | Theorems.Thm_KernelRamsey_nbhd_lt
-- name    : KernelRamsey.nbhd_lt
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:26:52.089071+00:00
-- url     : https://prove2.me/theorems/4fb43fd8-af07-4a86-80d6-b89d0e599a3a
-- title:
--   A vertex of a triangle-free set has fewer than $t$ neighbours
-- statement:
--   Let $A$ be a finite set of vertices of a graph that contains no triangle and no independent set of size $t$. Then every vertex $v \in A$ has fewer than $t$ neighbours in $A$. Indeed the neighbours of $v$ are pairwise non-adjacent, since two adjacent neighbours would form a triangle with $v$, so any $t$ of them would be an independent $t$-set.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
open Finset

theorem KernelRamsey.nbhd_lt {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] {t : Nat} {A : Finset V}
    (hnoT : ∀ T ⊆ A, ¬ G.IsNClique 3 T) (hnoI : ∀ I ⊆ A, ¬ Gᶜ.IsNClique t I)
    {v : V} (hv : v ∈ A) : (A.filter (fun w => G.Adj v w)).card < t := by sorry
