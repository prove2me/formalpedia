-- Prove2me | Theorems.Thm_GlobalTheory_exists_generatorScheme
-- name    : GlobalTheory.exists_generatorScheme
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:49.692588+00:00
-- url     : https://prove2.me/theorems/345b4f03-8603-4991-b870-16265687a869
-- title:
--   Global Theory: exists generator Scheme
-- statement:
--   The Global Theory construction uses the exists generator Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L414-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L414-L441

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
set_option backward.isDefEq.respectTransparency false
open GeneratorFunctor Opposite

theorem GlobalTheory.exists_generatorScheme : ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val := by sorry
