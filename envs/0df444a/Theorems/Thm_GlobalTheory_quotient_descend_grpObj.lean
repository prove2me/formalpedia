-- Prove2me | Theorems.Thm_GlobalTheory_quotient_descend_grpObj
-- name    : GlobalTheory.quotient_descend_grpObj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:15:58.316399+00:00
-- url     : https://prove2.me/theorems/1a1d9868-999d-4250-a8e1-bb0708c4f057
-- title:
--   Global Theory: quotient descend grp Obj
-- statement:
--   The Global Theory construction uses the quotient descend grp Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/QuotientDescendGrpObj.lean#L96-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/QuotientDescendGrpObj.lean#L96-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open QuotientDescent

theorem GlobalTheory.quotient_descend_grpObj :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).hom (τ g).hom ∧ ∀ c, (a.act c).left ≫ (τ g).hom = (τ g).hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by sorry
