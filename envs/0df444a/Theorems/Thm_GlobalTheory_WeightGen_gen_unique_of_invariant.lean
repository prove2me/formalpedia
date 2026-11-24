-- Prove2me | Theorems.Thm_GlobalTheory_WeightGen_gen_unique_of_invariant
-- name    : GlobalTheory.WeightGen.gen_unique_of_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:52:03.753932+00:00
-- url     : https://prove2.me/theorems/2969659f-ec3f-4751-98a0-01b5d14717b3
-- title:
--   Weight Gen: gen unique of invariant
-- statement:
--   The Weight Gen construction uses the gen unique of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L314-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L314-L351

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

theorem GlobalTheory.WeightGen.gen_unique_of_invariant {X Y P S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ ε φ' ε') (π : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ π = 𝟙 _) (a p : P ⟶ Y)
    (hp : ∀ f : Γ(Y, ⊤), a.appTop.hom f = p.appTop.hom f → ∃ c, π.appTop.hom c = f)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) (h : ∀ y J, Good M y J → val u e y J = val u' e y J)
    (hw : ∀ y J, Good M y J → val u a y J * (val u' a y J)⁻¹ = val u p y J * (val u' p y J)⁻¹)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by sorry
