-- Prove2me | Theorems.Thm_KernelRamsey_ram2_step
-- name    : KernelRamsey.ram2_step
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:28.807939+00:00
-- url     : https://prove2.me/theorems/26797253-e8d0-4226-9a9a-26b8e3789d96
-- title:
--   The recurrence $R(s,t) \le R(s-1,t) + R(s,t-1)$
-- statement:
--   Let $s,t \ge 2$ and $a+b \ge 1$. Suppose that in every graph every set of at least $a$ vertices contains an $(s-1)$-clique or an independent $t$-set, and that in every graph every set of at least $b$ vertices contains an $s$-clique or an independent $(t-1)$-set. Then in every graph every set of at least $a+b$ vertices contains an $s$-clique or an independent $t$-set. This is the neighbourhood recurrence for Ramsey numbers.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.ram2_step {s t a b : Nat} (hs : 2 ≤ s) (ht : 2 ≤ t) (hab : 1 ≤ a + b)
    (ha : Ram2 (s - 1) t a) (hb : Ram2 s (t - 1) b) : Ram2 s t (a + b) := by sorry
