-- Prove2me | Theorems.Thm_GlobalTheory_polarised_lattice_eighth_power
-- name    : GlobalTheory.polarised_lattice_eighth_power
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:10.252174+00:00
-- url     : https://prove2.me/theorems/aa29b1b6-d70b-4964-b9fa-6fa7ace79c98
-- title:
--   Global Theory: polarised lattice eighth power
-- statement:
--   The Global Theory construction uses the polarised lattice eighth power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L143-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEquivPiRangeOfMatrixUnits.lean#L143-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.polarised_lattice_eighth_power :
    ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (r a x)) → (∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (e : La ≃+ (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef ∧ (∀ x u i, hh (Q x) (σ (u, i)) = τ.mulVec (fun i' => (e x u (.inl i') : ℂ)) i + (e x u (.inr i) : ℂ)) ∧ (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (e x u) (e y v)) ∧ ∀ a x u, e (r a x) u = ∑ v, a u v • e x v := by sorry
