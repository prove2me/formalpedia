-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_inverseBundleGeneratorPoint_ofChartUnits_sections
-- name    : GlobalTheory.GeneratorFunctor.Pt.inverseBundleGeneratorPoint_ofChartUnits_sections
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:53:45.707458+00:00
-- url     : https://prove2.me/theorems/0b930d60-a51d-44af-b989-cf59872a4b56
-- title:
--   Pt: inverse Bundle Generator Point of Chart Units sections
-- statement:
--   The Pt construction uses the inverse Bundle Generator Point of Chart Units sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L342-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L342-L349

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}

theorem GlobalTheory.GeneratorFunctor.Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (hN : ∀ k, (N k).IsLB) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hb : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (v : κ → Γ(Z, ⊤)ˣ) (k)
    {T : Scheme.{0}} (a : T ⟶ Z) (h) :
    (pb a _ ⊤ h ((Pt.ofChart hN b j hb v).s k (j k))).val = a.appTop.hom (v k).val := by sorry
