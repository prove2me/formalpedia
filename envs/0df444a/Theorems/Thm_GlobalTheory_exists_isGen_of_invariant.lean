-- Prove2me | Theorems.Thm_GlobalTheory_exists_isGen_of_invariant
-- name    : GlobalTheory.exists_isGen_of_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:15.954348+00:00
-- url     : https://prove2.me/theorems/cc9a867b-2823-4cc3-83d1-c79bc840de05
-- title:
--   Global Theory: exists is Gen of invariant
-- statement:
--   The Global Theory construction uses the exists is Gen of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIsGenOfInvariant.lean#L28-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIsGenOfInvariant.lean#L28-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_isGen_of_invariant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by sorry
