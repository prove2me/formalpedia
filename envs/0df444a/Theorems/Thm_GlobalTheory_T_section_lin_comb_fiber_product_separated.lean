-- Prove2me | Theorems.Thm_GlobalTheory_T_section_lin_comb_fiber_product_separated
-- name    : GlobalTheory.T.section_lin_comb_fiber_product_separated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:34.257799+00:00
-- url     : https://prove2.me/theorems/48b5f251-e29c-4ae6-ac33-881aca3a6d78
-- title:
--   T: section lin comb fiber product separated
-- statement:
--   The T construction uses the section lin comb fiber product separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparatedStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparatedStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.section_lin_comb_fiber_product_separated : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of F))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ), (∀ v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂)), ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (r : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → sval v r z J = ∑ i, sval (a i) (r ≫ (fst Y₁ Y₂).left) z J * sval (b i) (r ≫ (snd Y₁ Y₂).left) z J) ∧ ∀ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ c : Fin n → F, (∀ j, ∑ i, resTop _ (scal Y₁.hom (c i)) * (a i).f j = 0) → c = 0) → (∀ (z : (Y₁ ⊗ Y₂).left) (J), Good L z J → ∑ i, sval (a i) (fst Y₁ Y₂).left z J * sval (b i) (snd Y₁ Y₂).left z J = 0) → ∀ i j, (b i).f j = 0 := by sorry
