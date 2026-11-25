-- Prove2me | Theorems.Thm_GlobalTheory_HolTorsion_isHolTo_of_isPullback
-- name    : GlobalTheory.HolTorsion.isHolTo_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:42:02.269395+00:00
-- url     : https://prove2.me/theorems/42325469-c9d6-409e-a6eb-c8489f3fd17a
-- title:
--   Hol Torsion: is Hol To of is Pullback
-- statement:
--   The Hol Torsion construction uses the is Hol To of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L33-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L33-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTorsion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}

theorem GlobalTheory.HolTorsion.isHolTo_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} (ha : IsHolTo B fun w => c w ≫ p)
    (hb : IsHolTo B fun w => c w ≫ q) : IsHolTo B c := by sorry
