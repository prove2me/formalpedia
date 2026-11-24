-- Prove2me | Theorems.Thm_KernelRamsey_ram2_34
-- name    : KernelRamsey.ram2_34
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:32.600265+00:00
-- url     : https://prove2.me/theorems/aefa973f-07dd-461b-b575-c860dd372426
-- title:
--   The statement $R(3,4) \le 9$ in the general form
-- statement:
--   In every graph, every set of at least $9$ vertices contains a triangle or an independent set of size $4$, stated for cliques of size $3$ and independent sets of size $4$ in the general predicate used by the recurrence.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram2_34 : Ram2 3 4 9 := by sorry
