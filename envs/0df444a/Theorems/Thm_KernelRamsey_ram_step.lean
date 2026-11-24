-- Prove2me | Theorems.Thm_KernelRamsey_ram_step
-- name    : KernelRamsey.ram_step
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:04.111812+00:00
-- url     : https://prove2.me/theorems/4026d3ca-d820-422d-9adb-309dd4f11b7d
-- title:
--   The degree step for $R(3,t)$
-- statement:
--   Suppose every set of at least $m$ vertices of every graph contains a triangle or an independent $(t-1)$-set. Then every set of at least $m+t$ vertices of every graph contains a triangle or an independent $t$-set. In terms of Ramsey numbers this is $R(3,t) \le R(3,t-1) + t$. The proof uses that a vertex of a triangle-free set has fewer than $t$ neighbours, and applies the hypothesis to its non-neighbours.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram_step {t m : Nat} (h : Ram (t - 1) m) (ht : 1 ≤ t) : Ram t (m + t) := by sorry
