-- Prove2me | Theorems.Thm_KernelRamsey_ram2_43
-- name    : KernelRamsey.ram2_43
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:33.633008+00:00
-- url     : https://prove2.me/theorems/84d90564-b127-41a4-a9f3-b75369333ac0
-- title:
--   The statement $R(4,3) \le 9$
-- statement:
--   In every graph, every set of at least $9$ vertices contains a $4$-clique or an independent set of size $3$. This is the mirror image of $R(3,4) \le 9$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram2_43 : Ram2 4 3 9 := by sorry
