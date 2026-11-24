-- Prove2me | Theorems.Thm_KernelRamsey_even_card_adjacent_pairs
-- name    : KernelRamsey.even_card_adjacent_pairs
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:18.413781+00:00
-- url     : https://prove2.me/theorems/bc0bb858-4bbb-4539-8cde-a2c5d0a5336e
-- title:
--   The number of ordered adjacent pairs in a vertex set is even
-- statement:
--   For a finite set $B$ of vertices of a simple graph, the number of ordered pairs $(a,b) \in B \times B$ with $a$ adjacent to $b$ is even. Swapping the two entries of a pair is an involution without fixed points on this set, because no vertex is adjacent to itself.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
open Finset

theorem KernelRamsey.even_card_adjacent_pairs {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : Even (((B ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card) := by sorry
