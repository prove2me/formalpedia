-- Prove2me | Theorems.Thm_GlobalTheory_WeightGen_exists_normalised
-- name    : GlobalTheory.WeightGen.exists_normalised
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:23.435281+00:00
-- url     : https://prove2.me/theorems/574c2747-36c7-44f6-9944-bdfd9d9d4116
-- title:
--   Weight Gen: exists normalised
-- statement:
--   The Weight Gen construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L378-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L378-L455

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
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.WeightGen.exists_normalised {T S₀ P : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (π : T ⟶ S₀)
    (e : S₀ ⟶ T) (he : e ≫ π = 𝟙 _) (heq : e ≫ q = 1) (a p : P ⟶ T) (hq : a ≫ q = p ≫ q)
    (hπ : a ≫ π = p ≫ π)
    (hp : ∀ f : Γ(T.left, ⊤), a.left.appTop.hom f = p.left.appTop.hom f →
      ∃ c, π.left.appTop.hom c = f)
    (c : D.X → GermFn P.left)
    (hc : ∀ χ χ' Z r z, c (χ + χ') Z r z = c χ Z r z * c χ' Z r z)
    (H : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val t (r ≫ a.left) z J = c χ Z r z * val t (r ≫ p.left) z J) :
    ∃ t : ∀ χ, LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), (∀ χ, (t χ).IsGen) ∧
      (∀ χ χ', LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
            (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') q)).left))
        (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) ∧
      (∀ χ y J, Good D.P.L y J → val (t χ) e.left y J = 1) ∧
      ∀ χ (Z : Scheme.{0}) (r : Z ⟶ P.left) (z : Z) (J), Good D.P.L z J →
        val (t χ) (r ≫ a.left) z J = c χ Z r z * val (t χ) (r ≫ p.left) z J := by sorry
