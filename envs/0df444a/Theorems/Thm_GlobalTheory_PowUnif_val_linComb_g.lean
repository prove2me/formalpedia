-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_val_linComb_g
-- name    : GlobalTheory.PowUnif.val_linComb_g
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:28.121769+00:00
-- url     : https://prove2.me/theorems/9f3d049e-bf9c-4144-ac3f-3e23f5267567
-- title:
--   Pow Unif: val lin Comb g
-- statement:
--   The Pow Unif construction uses the val lin Comb g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L121-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {X Y : Scheme.{0}}

theorem GlobalTheory.PowUnif.val_linComb_g (x : Sp ℂ ⟶ Y) (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (jj jj' : K → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ jj ⊓ LB.wchart L φ jj')) :
    valAt' x (LB.wchart L φ jj ⊓ LB.wchart L φ jj') ((LB.LinComb L φ (fun _ => 1)).g jj jj').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val := by sorry
