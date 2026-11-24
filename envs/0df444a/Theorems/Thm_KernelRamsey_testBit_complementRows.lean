-- Prove2me | Theorems.Thm_KernelRamsey_testBit_complementRows
-- name    : KernelRamsey.testBit_complementRows
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:02.806893+00:00
-- url     : https://prove2.me/theorems/153eac93-9671-44cb-9e8d-a8161d2bede5
-- title:
--   Bits of the complement rows of a bit-mask graph
-- statement:
--   A graph on vertices $0,\dots,n-1$ is stored as a list of natural numbers, where bit $j$ of entry $i$ says that $j$ is a neighbour of $i$. The complement rows of the list are defined by clearing the neighbours of $i$ and the bit $i$ itself within the lowest $n$ bits. For $i, j < n$, bit $j$ of complement row $i$ is set exactly when bit $j$ of row $i$ is not set and $i \neq j$. This is the bridge that lets one clique search on the complement rows find independent sets of the original graph.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem KernelRamsey.testBit_complementRows {n : Nat} (rows : List Nat) (i j : Fin n) :
    (row (complementRows n rows) i.val).testBit j.val =
      (!(row rows i.val).testBit j.val && decide (i.val ≠ j.val)) := by sorry
