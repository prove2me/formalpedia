-- Prove2me | Theorems.Thm_GlobalTheory_T_thetaFunction_ne_zero_at_divisionPoint_selfDual
-- name    : GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:47.176351+00:00
-- url     : https://prove2.me/theorems/544dbeb1-0b2c-5675-b33a-0d0645791cbc
-- title:
--   T: theta Function ne zero at division Point self Dual
-- statement:
--   The T construction uses the theta Function ne zero at division Point self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDualStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaFunctionNeZeroAtDivisionPointSelfDualStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDualStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by sorry
