-- Prove2me | Theorems.Thm_GlobalTheory_SectionsProduct_le_wchart_sum
-- name    : GlobalTheory.SectionsProduct.le_wchart_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:38.963173+00:00
-- url     : https://prove2.me/theorems/a8ed749f-a4c2-4b8b-a5fe-9d32f83c616a
-- title:
--   Sections Product: le wchart sum
-- statement:
--   The Sections Product construction uses the le wchart sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L258-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L258-L263

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
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
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (X₁ ⟶ B)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (X₂ ⟶ B)) (ε₂ : K₂ → ℤ)

theorem GlobalTheory.SectionsProduct.le_wchart_sum {U : X₁.Opens} {V : X₂.Opens} {j : K₁ → L.ι} {k : K₂ → L.ι} (hU : U ≤ LB.wchart L φ₁ j)
    (hV : V ≤ LB.wchart L φ₂ k) : p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V ≤
      LB.wchart L (Sum.elim (fun k => p ≫ φ₁ k) (fun k => q ≫ φ₂ k)) (Sum.elim j k) := by sorry
