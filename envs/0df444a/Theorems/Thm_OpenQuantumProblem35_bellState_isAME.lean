-- Prove2me | Theorems.Thm_OpenQuantumProblem35_bellState_isAME
-- name    : OpenQuantumProblem35.bellState_isAME
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:43.482307+00:00
-- url     : https://prove2.me/theorems/82d83aab-238e-412b-8190-983ec82b9057
-- title:
--   Open Quantum Problem35: bell State is AME
-- statement:
--   The standard Bell state is $\mathrm{AME}(2,d)$ for every physical local dimension $d \ge 2$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L623-L626
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L623-L626

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.bellState_isAME {d : ℕ} (hd : 2 ≤ d) :
    IsAME (n := 2) (d := d) (bellState d) := by sorry
