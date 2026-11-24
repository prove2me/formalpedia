-- Prove2me | Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale
-- name    : GlobalTheory.exists_holomorphic_section_of_etale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:01.446493+00:00
-- url     : https://prove2.me/theorems/8fae3b62-11a2-41f2-ae78-85d7a05169fe
-- title:
--   Global Theory: exists holomorphic section of etale
-- statement:
--   The Global Theory construction uses the exists holomorphic section of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTestFunctionsSubsetOfMemNhds.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTestFunctionsSubsetOfMemNhds.lean#L27-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints

theorem GlobalTheory.exists_holomorphic_section_of_etale :
    (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) := by sorry
