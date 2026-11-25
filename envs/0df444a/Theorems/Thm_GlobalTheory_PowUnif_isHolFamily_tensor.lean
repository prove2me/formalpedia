-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_isHolFamily_tensor
-- name    : GlobalTheory.PowUnif.isHolFamily_tensor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:10.097904+00:00
-- url     : https://prove2.me/theorems/01550243-6e30-44d2-839b-33ad0fbe4668
-- title:
--   Pow Unif: is Hol Family tensor
-- statement:
--   The Pow Unif construction uses the is Hol Family tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L39-L47

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.PowUnif.isHolFamily_tensor (X Y : Over (Sp ℂ)) (c : E → (𝟙_ (Over (Sp ℂ)) ⟶ X ⊗ Y))
    (h0 : IsHolFamily (Z := X.left) (fun z => (c z ≫ fst _ _).left))
    (h1 : IsHolFamily (Z := Y.left) (fun z => (c z ≫ snd _ _).left)) :
    IsHolFamily (Z := (X ⊗ Y).left) (fun z => (c z).left) := by sorry
