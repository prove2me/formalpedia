-- Prove2me | Theorems.Thm_KernelRamsey_ram2_44
-- name    : KernelRamsey.ram2_44
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:32.495322+00:00
-- url     : https://prove2.me/theorems/f227ca33-530f-44c7-941c-0f99d8d206c5
-- title:
--   Every set of 18 vertices contains a 4-clique or an independent 4-set
-- statement:
--   In every graph, every set of at least $18$ vertices contains a $4$-clique or an independent set of size $4$. This is the upper bound $R(4,4) \le 18$, from the recurrence $R(4,4) \le R(3,4) + R(4,3) = 9 + 9$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram2_44 : Ram2 4 4 18 := by sorry
