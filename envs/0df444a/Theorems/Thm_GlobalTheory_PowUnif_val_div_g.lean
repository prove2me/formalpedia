-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_val_div_g
-- name    : GlobalTheory.PowUnif.val_div_g
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:10.860635+00:00
-- url     : https://prove2.me/theorems/c36d2935-aa4f-4485-982d-c05bc11edf46
-- title:
--   Pow Unif: val div g
-- statement:
--   The Pow Unif construction uses the val div g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L112-L119

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

theorem GlobalTheory.PowUnif.val_div_g (M L : LB X) (x : Sp ℂ ⟶ X) (a a' : M.ι) (b b' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) :
    valAt' x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')).val =
      valAt' x (M.U a ⊓ M.U a') (M.g a a').val * (valAt' x (L.U b ⊓ L.U b') (L.g b b').val)⁻¹ := by sorry
