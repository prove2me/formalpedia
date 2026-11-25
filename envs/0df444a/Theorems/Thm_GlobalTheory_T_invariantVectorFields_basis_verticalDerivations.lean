-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantVectorFields_basis_verticalDerivations
-- name    : GlobalTheory.T.invariantVectorFields_basis_verticalDerivations
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:46.288367+00:00
-- url     : https://prove2.me/theorems/66a860b7-360e-5bae-a7e9-58d1922e977f
-- title:
--   T: invariant Vector Fields basis vertical Derivations
-- statement:
--   The T construction uses the invariant Vector Fields basis vertical Derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsBasisVerticalDerivationsStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InvariantVectorFieldsBasisVerticalDerivationsStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
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

theorem GlobalTheory.T.invariantVectorFields_basis_verticalDerivations : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (T : Scheme.{0}) (y : T ⟶ A₀.left) (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(T, (y ≫ m) ⁻¹ᵁ W)), LocDerK (y ≫ A₀.hom) p (y ≫ m) (fun _ => 0) W₀ d → ∃! c : Fin g → Γ(T, (y ≫ m) ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by sorry
