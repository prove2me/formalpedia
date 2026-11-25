-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_siegel_fock_form_of_complex_structure
-- name    : GlobalTheory.T.exists_siegel_fock_form_of_complex_structure
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:53.686715+00:00
-- url     : https://prove2.me/theorems/61623c06-2760-591f-8339-ef9a680ef42d
-- title:
--   T: exists siegel fock form of complex structure
-- statement:
--   The T construction uses the exists siegel fock form of complex structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelFockFormOfComplexStructureStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSiegelFockFormOfComplexStructureStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelFockFormOfComplexStructure
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelFockFormOfComplexStructureStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_siegel_fock_form_of_complex_structure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by sorry
