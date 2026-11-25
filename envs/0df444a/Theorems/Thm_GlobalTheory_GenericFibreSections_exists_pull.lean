-- Prove2me | Theorems.Thm_GlobalTheory_GenericFibreSections_exists_pull
-- name    : GlobalTheory.GenericFibreSections.exists_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:31.297592+00:00
-- url     : https://prove2.me/theorems/33aec8db-7855-4815-9448-7b91749ef729
-- title:
--   Generic Fibre Sections: exists pull
-- statement:
--   The Generic Fibre Sections construction uses the exists pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L79-L84

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
import Theorems.Thm_GlobalTheory_UU_exists_pull

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

theorem GlobalTheory.GenericFibreSections.exists_pull (h : Y' ⟶ Y) (φ : Y ⟶ X₁) (φ' : Y' ⟶ X₁) (e : φ' = h ≫ φ) (k : ℤ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ') (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L₁ z J → sval s' r z J = sval s (r ≫ h) z J := by sorry
