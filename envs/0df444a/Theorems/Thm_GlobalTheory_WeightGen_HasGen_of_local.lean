-- Prove2me | Theorems.Thm_GlobalTheory_WeightGen_HasGen_of_local
-- name    : GlobalTheory.WeightGen.HasGen.of_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:16.53736+00:00
-- url     : https://prove2.me/theorems/0c75d02f-887a-4c99-bcf3-11286fbac694
-- title:
--   Has Gen: of local
-- statement:
--   The Has Gen construction uses the of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L33-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L33-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
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
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}

theorem GlobalTheory.WeightGen.HasGen.of_local (h : a ≫ q = p ≫ q) {N : LB B} {c : GermFn P} {A : Type} (W : A → B.Opens)
    (hW : ∀ x, ∃ α, x ∈ W α) (F : N.ι → A → GermFn G)
    (rep : ∀ j α, ∃ y : Γ(G, q ⁻¹ᵁ N.U j ⊓ q ⁻¹ᵁ W α)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z),
      q (r z) ∈ N.U j → q (r z) ∈ W α → gm r z _ y = F j α Z r z)
    (tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G) (z : Z) (j j' : N.ι) (α α' : A), q (r z) ∈ N.U j →
      q (r z) ∈ N.U j' → q (r z) ∈ W α → q (r z) ∈ W α' →
      F j' α' Z r z = gm (r ≫ q) z _ (N.g j j') * F j α Z r z)
    (wt : ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : N.ι) (α : A), q (p (r z)) ∈ N.U j →
      q (p (r z)) ∈ W α → F j α Z (r ≫ a) z = c Z r z * F j α Z (r ≫ p) z) :
    HasGen q a p N c := by sorry
