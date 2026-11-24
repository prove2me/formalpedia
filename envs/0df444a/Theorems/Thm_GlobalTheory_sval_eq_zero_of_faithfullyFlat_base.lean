-- Prove2me | Theorems.Thm_GlobalTheory_sval_eq_zero_of_faithfullyFlat_base
-- name    : GlobalTheory.sval_eq_zero_of_faithfullyFlat_base
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:46.323399+00:00
-- url     : https://prove2.me/theorems/45aa02f3-819f-4359-bce0-859bf7d8bf8e
-- title:
--   Global Theory: sval eq zero of faithfully Flat base
-- statement:
--   The Global Theory construction uses the sval eq zero of faithfully Flat base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfFaithfullyFlatBase.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalEqZeroOfFaithfullyFlatBase.lean#L28-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfFaithfullyFlatBase
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
open GlobalTheory

theorem GlobalTheory.sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by sorry
