-- Prove2me | Theorems.Thm_GlobalTheory_TensorSiegel_tensor_siegel_lattices
-- name    : GlobalTheory.TensorSiegel.tensor_siegel_lattices
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:35.261794+00:00
-- url     : https://prove2.me/theorems/04747381-458a-48d4-87af-2998c695a6e3
-- title:
--   Tensor Siegel: tensor siegel lattices
-- statement:
--   The Tensor Siegel construction uses the tensor siegel lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L397-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveTensorOmegaStd.lean#L397-L423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TensorSiegel

theorem GlobalTheory.TensorSiegel.tensor_siegel_lattices : ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) → Function.Bijective EF ∧ (∀ τ : Matrix (Fin h) (Fin h) ℂ, (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → ∃ (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y)) ∧ (∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (Q Q' : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∀ x u i, Q' x (σ (u, i)) = (τ').mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q' x = e (Q x)) → τ = τ') ∧ ∀ a : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (fun u => ∑ v, a u v • x v)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by sorry
