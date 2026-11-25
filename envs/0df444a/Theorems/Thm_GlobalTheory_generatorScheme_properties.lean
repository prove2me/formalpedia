-- Prove2me | Theorems.Thm_GlobalTheory_generatorScheme_properties
-- name    : GlobalTheory.generatorScheme_properties
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:06.198599+00:00
-- url     : https://prove2.me/theorems/4c595495-497b-47bc-a052-829d2af9200b
-- title:
--   Global Theory: generator Scheme properties
-- statement:
--   The Global Theory construction uses the generator Scheme properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L224-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L224-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory

theorem GlobalTheory.generatorScheme_properties :
    ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∀ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q ∧ Smooth q ∧ Surjective q ∧ IsSeparated q ∧ GeometricallyConnected q := by sorry
