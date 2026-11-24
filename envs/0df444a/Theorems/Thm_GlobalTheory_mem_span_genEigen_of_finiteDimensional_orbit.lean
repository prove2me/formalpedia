-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_genEigen_of_finiteDimensional_orbit
-- name    : GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:20.963798+00:00
-- url     : https://prove2.me/theorems/ea563e76-cd83-4378-bef2-2089c2157d4b
-- title:
--   Global Theory: mem span gen Eigen of finite Dimensional orbit
-- statement:
--   The Global Theory construction uses the mem span gen Eigen of finite Dimensional orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L122-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L122-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GenEigenFinOrbit

theorem GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by sorry
