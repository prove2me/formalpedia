-- Prove2me | Theorems.Thm_KernelRamsey_ram_two_three
-- name    : KernelRamsey.ram_two_three
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:04.48693+00:00
-- url     : https://prove2.me/theorems/a4de30ef-4084-4200-94e7-8756a28ec73b
-- title:
--   Three vertices contain a triangle or a non-adjacent pair
-- statement:
--   In every graph, every set of at least $3$ vertices contains a triangle or two distinct non-adjacent vertices. Equivalently, if every pair among three vertices is adjacent, they form a triangle. This is the base case `Ram 2 3` of the degree argument for $R(3,t)$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram_two_three : Ram 2 3 := by sorry
