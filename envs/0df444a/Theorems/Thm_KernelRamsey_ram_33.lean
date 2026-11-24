-- Prove2me | Theorems.Thm_KernelRamsey_ram_33
-- name    : KernelRamsey.ram_33
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:06.389534+00:00
-- url     : https://prove2.me/theorems/44a014a7-a85f-4ace-9e5f-244a18ce2a59
-- title:
--   Every set of 6 vertices contains a triangle or an independent triple
-- statement:
--   In every graph, every set of at least $6$ vertices contains a triangle or an independent set of size $3$. This is the upper bound $R(3,3) \le 6$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram_33 : Ram 3 6 := by sorry
