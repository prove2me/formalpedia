-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_val_iso
-- name    : GlobalTheory.PowUnif.val_iso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:02.165942+00:00
-- url     : https://prove2.me/theorems/2825be9d-3ca9-4190-8def-6cecbd937acd
-- title:
--   Pow Unif: val iso
-- statement:
--   The Pow Unif construction uses the val iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L129-L142

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

theorem GlobalTheory.PowUnif.val_iso (x : Sp ℂ ⟶ Y) (L : LB X) (L' : LB Y) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (w : LB.Iso L' (LB.LinComb L φ (fun _ => 1))) (hw : w.IsGen) (jj jj' : K → L.ι) (b b' : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj) (h₂ : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ jj')
    (h₃ : ⊤ ≤ x ⁻¹ᵁ L'.U b) (h₄ : ⊤ ≤ x ⁻¹ᵁ L'.U b') :
    valAt' x (LB.wchart L φ jj ⊓ L'.U b) (w.s (jj, b)).val =
      (∏ k, valAt' (x ≫ φ k) (L.U (jj k) ⊓ L.U (jj' k)) (L.g (jj k) (jj' k)).val) *
        (valAt' x (L'.U b ⊓ L'.U b') (L'.g b b').val)⁻¹ *
        valAt' x (LB.wchart L φ jj' ⊓ L'.U b') (w.s (jj', b')).val := by sorry
