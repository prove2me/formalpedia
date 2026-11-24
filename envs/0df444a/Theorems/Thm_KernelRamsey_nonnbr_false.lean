-- Prove2me | Theorems.Thm_KernelRamsey_nonnbr_false
-- name    : KernelRamsey.nonnbr_false
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:04.598234+00:00
-- url     : https://prove2.me/theorems/60aacf9b-79a4-446e-b1c9-b450f3d4e264
-- title:
--   Non-neighbours of a vertex cannot be Ramsey-large
-- statement:
--   Let $A$ be a finite set of vertices with no triangle and no independent $t$-set, let $v \in A$, and let $M$ be the elements of $A$ other than $v$ that are not adjacent to $v$. If every set of at least $m$ vertices of every graph contains a triangle or an independent $(t-1)$-set, then $|M| < m$. A triangle in $M$ lies in $A$, and an independent $(t-1)$-set in $M$ together with $v$ is an independent $t$-set in $A$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.nonnbr_false {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] {t m : Nat} (h : Ram (t - 1) m) (ht : 1 ≤ t) {A : Finset V}
    (hnoT : ∀ T ⊆ A, ¬ G.IsNClique 3 T) (hnoI : ∀ I ⊆ A, ¬ Gᶜ.IsNClique t I)
    {v : V} (hv : v ∈ A) (hM : m ≤ (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card) : False := by sorry
