-- Prove2me | Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
-- name    : OpenQuantumProblem35.mkStateVector_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:51.280352+00:00
-- url     : https://prove2.me/theorems/854946a4-94d0-5910-83a5-69d8653ed169
-- title:
--   Open Quantum Problem35: mk State Vector apply
-- statement:
--   A state built from amplitudes has those amplitudes as its coordinates.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L124-L125
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L124-L125

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.mkStateVector_apply {n d : ℕ} (ψ : Config n d → ℂ) (x : Config n d) :
    mkStateVector ψ x = ψ x := by sorry

attribute [defeq] OpenQuantumProblem35.mkStateVector_apply
