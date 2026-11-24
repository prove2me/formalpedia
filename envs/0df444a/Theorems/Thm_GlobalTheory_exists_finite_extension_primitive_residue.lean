-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_extension_primitive_residue
-- name    : GlobalTheory.exists_finite_extension_primitive_residue
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:17.9902+00:00
-- url     : https://prove2.me/theorems/a63b48f6-f2f9-4aea-85cf-74bcf9d667f2
-- title:
--   Global Theory: exists finite extension primitive residue
-- statement:
--   The Global Theory construction uses the exists finite extension primitive residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteExtensionPrimitiveResidue.lean#L33-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFiniteExtensionPrimitiveResidue.lean#L33-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteExtensionPrimitiveResidue
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

theorem GlobalTheory.exists_finite_extension_primitive_residue :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V], (∃ n : ℕ, n.Prime ∧ IsUnit (n : V)) ∧ ∀ (n j : ℕ), n.Prime → IsUnit (n : V) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (ζ : W), (Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) ∧ Function.Injective φ.left.appTop.hom ∧ IsUnit (n : W) ∧ ζ ^ (n ^ j) = 1 ∧ IsPrimitiveRoot (IsLocalRing.residue W ζ) (n ^ j) := by sorry
