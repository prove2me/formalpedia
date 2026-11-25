-- Prove2me | Theorems.Thm_GlobalTheory_isDerivAt0_fibre
-- name    : GlobalTheory.isDerivAt0_fibre
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:10.695618+00:00
-- url     : https://prove2.me/theorems/ec6e16b7-44e7-5642-964f-1a59bcad4ed3
-- title:
--   Global Theory: is Deriv At0 fibre
-- statement:
--   The Global Theory construction uses the is Deriv At0 fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDerivAt0OfIsPullback.lean#L234-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDerivAt0OfIsPullback.lean#L234-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open FibreDeriv

theorem GlobalTheory.isDerivAt0_fibre :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Y : Scheme.{0}) (φ : Y ⟶ G.left) (s : Y ⟶ Sp ℂ) (e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)), IsPullback φ s G.hom y → (∀ z, e₁ z ≫ φ = (e z).left ∧ e₁ z ≫ s = 𝟙 _) → IsHolTo Set.univ (fun z => (e z).left) → ((∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ((∀ w, ∃! v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧ IsDerivAt0 e₁ w v) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e₁ 0 → ∃! w, IsDerivAt0 e₁ w v) := by sorry
