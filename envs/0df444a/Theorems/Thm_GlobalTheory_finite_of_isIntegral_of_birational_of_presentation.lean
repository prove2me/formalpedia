-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isIntegral_of_birational_of_presentation
-- name    : GlobalTheory.finite_of_isIntegral_of_birational_of_presentation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:13.832608+00:00
-- url     : https://prove2.me/theorems/50e62214-de86-416b-959b-9183b758a95a
-- title:
--   Global Theory: finite of is Integral of birational of presentation
-- statement:
--   The Global Theory construction uses the finite of is Integral of birational of presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FiniteOfIsIntegralOfBirationalOfPresentation.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FiniteOfIsIntegralOfBirationalOfPresentation.lean#L80-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FiniteOfIsIntegralOfBirationalOfPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.finite_of_isIntegral_of_birational_of_presentation :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) := by sorry
