-- Prove2me | Theorems.Thm_OpenQuantumProblem35_maximallyMixed_apply
-- name    : OpenQuantumProblem35.maximallyMixed_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:30.202688+00:00
-- url     : https://prove2.me/theorems/0e5fe375-9347-4391-8970-adc5c55a37c9
-- title:
--   Open Quantum Problem35: maximally Mixed apply
-- statement:
--   The matrix entries of the maximally mixed state are diagonal and equal to the inverse subsystem dimension.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L280-L286
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L280-L286

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.maximallyMixed_apply {m d : ℕ} (x y : Config m d) :
    maximallyMixed m d x y =
      if x = y then ((Fintype.card (Config m d) : ℂ)⁻¹) else 0 := by sorry
