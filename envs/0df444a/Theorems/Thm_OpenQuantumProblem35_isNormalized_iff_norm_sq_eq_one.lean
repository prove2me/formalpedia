-- Prove2me | Theorems.Thm_OpenQuantumProblem35_isNormalized_iff_norm_sq_eq_one
-- name    : OpenQuantumProblem35.isNormalized_iff_norm_sq_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:00.1658+00:00
-- url     : https://prove2.me/theorems/d96c8c27-6346-5d6c-92bc-09dd47752f85
-- title:
--   Open Quantum Problem35: is Normalized iff norm sq eq one
-- statement:
--   A state is normalized iff its squared $L^2$ norm is $1$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L132-L149
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L132-L149

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.isNormalized_iff_norm_sq_eq_one {n d : ℕ} (ψ : StateVector n d) :
    IsNormalized ψ ↔ ‖ψ‖ ^ 2 = 1 := by sorry
