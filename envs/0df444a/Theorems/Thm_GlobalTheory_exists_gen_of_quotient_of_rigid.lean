-- Prove2me | Theorems.Thm_GlobalTheory_exists_gen_of_quotient_of_rigid
-- name    : GlobalTheory.exists_gen_of_quotient_of_rigid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:35.158446+00:00
-- url     : https://prove2.me/theorems/9ae9410a-190e-44bf-90cf-73ff3991bace
-- title:
--   Global Theory: exists gen of quotient of rigid
-- statement:
--   The Global Theory construction uses the exists gen of quotient of rigid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L184-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfQuotientOfRigid.lean#L184-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
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
open GenDescent

theorem GlobalTheory.exists_gen_of_quotient_of_rigid :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (P : Over X) (P' : Over X') (φ : P.left ⟶ P'.left) (e : X ⟶ P.left) (e' : X' ⟶ P'.left) (N : LB P'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ P.hom P'.hom π → Flat P'.hom → e ≫ P.hom = 𝟙 X → e' ≫ P'.hom = 𝟙 X' → e ≫ φ = π ≫ e' → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → N.IsLB → (∃ r : (N.pull e').Gen, r.IsGen) → (∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by sorry
