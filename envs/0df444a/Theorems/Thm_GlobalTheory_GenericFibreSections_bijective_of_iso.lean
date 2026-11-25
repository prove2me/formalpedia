-- Prove2me | Theorems.Thm_GlobalTheory_GenericFibreSections_bijective_of_iso
-- name    : GlobalTheory.GenericFibreSections.bijective_of_iso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:34.275825+00:00
-- url     : https://prove2.me/theorems/190355a6-7dd6-4e85-acee-f0af79aeb896
-- title:
--   Generic Fibre Sections: bijective of iso
-- statement:
--   The Generic Fibre Sections construction uses the bijective of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L100-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L100-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BijectiveOfIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.GenericFibreSections
variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem GlobalTheory.GenericFibreSections.bijective_of_iso (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (p : Y' ⟶ X₁) [IsIso f₁] [IsIso p]
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (Rel : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))) →
      LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))) → Prop)
    (hRel : ∀ σ t, Rel σ t ↔ ∀ (Z : Scheme.{0}) (rA : Z ⟶ Y') (y : Z ⟶ Y), rA ≫ p = y ≫ f₁ → ∀ (z : Z) J₁ J₂,
      Good L₁ z J₁ → Good L₂ z J₂ →
      (gw w y z (J₂ (y ≫ f₂)) (fun _ => J₁ (y ≫ f₁))).val ^ k * sval t rA z J₁ = sval σ y z J₂) :
    (∀ σ, ∃! t, Rel σ t) ∧ ∀ t, ∃! σ, Rel σ t := by sorry
