-- Prove2me | Theorems.Thm_KernelRamsey_card_split
-- name    : KernelRamsey.card_split
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:09.391197+00:00
-- url     : https://prove2.me/theorems/62d395cc-86f0-4ac3-a70b-1adc3853c155
-- title:
--   A set splits into a vertex, its neighbours and its non-neighbours
-- statement:
--   For a vertex $v$ in a finite set $A$ of vertices of a graph, $|A| = 1 + |N| + |M|$, where $N$ is the set of elements of $A$ adjacent to $v$ and $M$ is the set of elements of $A$ other than $v$ that are not adjacent to $v$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
open Finset

theorem KernelRamsey.card_split {V : Type} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (A : Finset V) {v : V} (hv : v ∈ A) :
    A.card = 1 + (A.filter (fun w => G.Adj v w)).card +
      (A.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)).card := by sorry
