-- Prove2me | Theorems.Thm_OpenQuantumProblem35_uniformCoeff_mul_star
-- name    : OpenQuantumProblem35.uniformCoeff_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:37.967294+00:00
-- url     : https://prove2.me/theorems/a18dd94d-6cc7-4684-9058-aa3e5974b877
-- title:
--   Open Quantum Problem35: uniform Coeff mul star
-- statement:
--   The squared norm of the uniform coefficient is the inverse local dimension.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L376-L384
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L376-L384

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.uniformCoeff_mul_star (d : ℕ) :
    uniformCoeff d * star (uniformCoeff d) = ((d : ℂ)⁻¹) := by sorry
