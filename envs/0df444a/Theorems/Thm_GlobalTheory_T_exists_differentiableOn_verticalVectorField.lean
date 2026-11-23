-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_differentiableOn_verticalVectorField
-- name    : GlobalTheory.T.exists_differentiableOn_verticalVectorField
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:52.86238+00:00
-- url     : https://prove2.me/theorems/5cb8507e-9fb1-4af9-b51d-e4701b14c0db
-- title:
--   T: exists differentiable On vertical Vector Field
-- statement:
--   The T construction uses the exists differentiable On vertical Vector Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnVerticalVectorFieldStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnVerticalVectorFieldStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_differentiableOn_verticalVectorField : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin P₀.g → ℂ)) (s : (Fin n → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ), IsOpen B → Differentiable ℂ G → (∀ z ∈ B, PtDer ((u.ex (G z)).left ≫ m) (s z) ∧ ∀ r, s z ⊤ (constFn p ⊤ r) = 0) → (∀ W f, DifferentiableOn ℂ (fun z => s z W f) {z ∈ B | G z ∈ dom u m W}) → ∃ w : (Fin n → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w B ∧ ∀ z ∈ B, ∀ W f, G z ∈ dom u m W → s z W f = fderiv ℂ (fn u m W f) (G z) (w z) := by sorry
