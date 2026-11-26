-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_isAME_of_div_two_eq_one
-- name    : OpenQuantumProblem35.diagonalState_isAME_of_div_two_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:04.797418+00:00
-- url     : https://prove2.me/theorems/c0297331-bdd4-4469-8140-2b480bbb86f8
-- title:
--   Open Quantum Problem35: diagonal State is AME of div two eq one
-- statement:
--   If $\lfloor n/2 \rfloor = 1$, then the diagonal state is $\mathrm{AME}(n,d)$ for every $d \ge 2$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L611-L620
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L611-L620

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_isAME_of_div_two_eq_one {n d : ℕ}
    (hn : 2 ≤ n) (hhalf : n / 2 = 1) (hd : 2 ≤ d) :
    IsAME (n := n) (d := d) (diagonalState n d) := by sorry
