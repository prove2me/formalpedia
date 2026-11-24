-- Prove2me | Theorems.Thm_KernelRamsey_ram_49
-- name    : KernelRamsey.ram_49
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:28.077467+00:00
-- url     : https://prove2.me/theorems/291167a8-914e-4cdc-9ff5-d7f2b2f4cb1d
-- title:
--   Every set of 9 vertices contains a triangle or an independent 4-set
-- statement:
--   In every graph, every set of at least $9$ vertices contains a triangle or an independent set of size $4$. This is the upper bound $R(3,4) \le 9$. The degree step alone gives only $10$. For $9$ vertices, a graph with no triangle and no independent $4$-set would have every degree at most $3$, and at least $3$ since the six non-neighbours of a vertex of smaller degree would contain an independent triple that extends to an independent $4$-set. So it would be $3$-regular on $9$ vertices, and the number of ordered adjacent pairs would be $27$, which is odd. This contradicts the evenness of that number.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram_49 : Ram 4 9 := by sorry
