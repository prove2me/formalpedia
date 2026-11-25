-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_eq_sum_mul_of_isDomain
-- name    : GlobalTheory.exists_smul_eq_sum_mul_of_isDomain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:42.199621+00:00
-- url     : https://prove2.me/theorems/17cffc2c-be28-4c49-aebe-4c7cced5c623
-- title:
--   Global Theory: exists smul eq sum mul of is Domain
-- statement:
--   The Global Theory construction uses the exists smul eq sum mul of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqSumMulOfIsDomain.lean#L85-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqSumMulOfIsDomain.lean#L85-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqSumMulOfIsDomain
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
noncomputable section
open GlobalTheory
open KunnethDomain ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.exists_smul_eq_sum_mul_of_isDomain : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of V))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [Flat Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] [Flat Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ) (v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂))), ∃ (r : V) (_ : r ≠ 0) (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → ∑ i, sval (a i) (ρ ≫ (fst Y₁ Y₂).left) z J * sval (b i) (ρ ≫ (snd Y₁ Y₂).left) z J = gs ρ z ⊤ (scal (Y₁ ⊗ Y₂).hom r) * sval v ρ z J := by sorry
