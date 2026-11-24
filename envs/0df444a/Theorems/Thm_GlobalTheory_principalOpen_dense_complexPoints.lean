-- Prove2me | Theorems.Thm_GlobalTheory_principalOpen_dense_complexPoints
-- name    : GlobalTheory.principalOpen_dense_complexPoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:11.011466+00:00
-- url     : https://prove2.me/theorems/558741df-9195-470b-b48f-4b12eef8b669
-- title:
--   Global Theory: principal Open dense complex Points
-- statement:
--   The Global Theory construction uses the principal Open dense complex Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PrincipalOpenDenseComplexPoints.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PrincipalOpenDenseComplexPoints.lean#L25-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PrincipalOpenDenseComplexPoints
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

theorem GlobalTheory.principalOpen_dense_complexPoints :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 → IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧ Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) := by sorry
