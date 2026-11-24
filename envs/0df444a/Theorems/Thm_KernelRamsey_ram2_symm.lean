-- Prove2me | Theorems.Thm_KernelRamsey_ram2_symm
-- name    : KernelRamsey.ram2_symm
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:28.867823+00:00
-- url     : https://prove2.me/theorems/eb7c85cc-0e0d-4662-9b5b-661106886736
-- title:
--   Swapping a graph and its complement swaps the two clique sizes
-- statement:
--   If every set of at least $m$ vertices of every graph contains an $s$-clique or an independent $t$-set, then every set of at least $m$ vertices of every graph contains a $t$-clique or an independent $s$-set. Apply the hypothesis to the complement graph.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram2_symm {s t m : Nat} (h : Ram2 s t m) : Ram2 t s m := by sorry
