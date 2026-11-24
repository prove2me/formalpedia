-- Prove2me | Theorems.Thm_KernelRamsey_ram_35
-- name    : KernelRamsey.ram_35
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:27.023649+00:00
-- url     : https://prove2.me/theorems/2a8cedc9-f04a-4a31-9096-1e34a4638ceb
-- title:
--   Every set of 14 vertices contains a triangle or an independent 5-set
-- statement:
--   In every graph, every set of at least $14$ vertices contains a triangle or an independent set of size $5$. This is the upper bound $R(3,5) \le 14$, obtained from $R(3,4) \le 9$ by the degree step.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram_35 : Ram 5 14 := by sorry
