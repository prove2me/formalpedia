-- Prove2me | Theorems.Thm_GlobalTheory_WeightGen_HasGen_exists_gen
-- name    : GlobalTheory.WeightGen.HasGen.exists_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:51.177985+00:00
-- url     : https://prove2.me/theorems/c72a1d6c-92dc-491b-a911-60b47238811c
-- title:
--   Has Gen: exists gen
-- statement:
--   The Has Gen construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L149-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L149-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen

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

theorem GlobalTheory.WeightGen.HasGen.exists_gen {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {c : GermFn P} (h : a ≫ q = p ≫ q)
    (H : HasGen q a p (LB.LinComb L φ ε) c) (φ' : K → (G ⟶ X)) (ε' : K → ℤ)
    (hφ : ∀ k, φ' k = q ≫ φ k) (hε : ∀ k, ε' k = -ε k) (hL : L.IsLB) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J),
      Good L z J → val t (r ≫ a) z J = c Z r z * val t (r ≫ p) z J := by sorry
