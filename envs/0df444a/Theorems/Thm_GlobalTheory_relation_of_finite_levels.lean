-- Prove2me | Theorems.Thm_GlobalTheory_relation_of_finite_levels
-- name    : GlobalTheory.relation_of_finite_levels
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:41.460587+00:00
-- url     : https://prove2.me/theorems/ec3ae4f3-b4e4-4624-ac02-b645915d3361
-- title:
--   Global Theory: relation of finite levels
-- statement:
--   The Global Theory construction uses the relation of finite levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RelationOfFiniteLevels.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RelationOfFiniteLevels.lean#L16-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
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

theorem GlobalTheory.relation_of_finite_levels : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by sorry
