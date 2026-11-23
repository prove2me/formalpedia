-- Prove2me | Theorems.Thm_GlobalTheory_tensor_sections_eq_zero_iff
-- name    : GlobalTheory.tensor_sections_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:48.961795+00:00
-- url     : https://prove2.me/theorems/8b390990-b1e0-44a3-ba69-7fe22c303da8
-- title:
--   Global Theory: tensor sections eq zero iff
-- statement:
--   The Global Theory construction uses the tensor sections eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSumTmulLinearIndependent.lean#L50-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSumTmulLinearIndependent.lean#L50-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory

theorem GlobalTheory.tensor_sections_eq_zero_iff : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) [QuasiCompact p₁] [IsSeparated p₁] [QuasiCompact p₂] [IsSeparated p₂] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) (n : ℕ) (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂)), (∑ i, TensorProduct.tmul F (a i) (b i) = 0) ↔ ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J → ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by sorry
