-- Prove2me | Theorems.Thm_GlobalTheory_HolTorsion_exists_isHolTo_lift
-- name    : GlobalTheory.HolTorsion.exists_isHolTo_lift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:02.861245+00:00
-- url     : https://prove2.me/theorems/e882de94-c1bd-4d6a-a1b0-825c6c027c8f
-- title:
--   Hol Torsion: exists is Hol To lift
-- statement:
--   The Hol Torsion construction uses the exists is Hol To lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L85-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L85-L95

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

theorem GlobalTheory.HolTorsion.exists_isHolTo_lift {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {a : E → (Sp ℂ ⟶ X)} {a' : E → (Sp ℂ ⟶ Y)} (ha : IsHolTo B a) (ha' : IsHolTo B a')
    (h : ∀ w ∈ B, a w ≫ s = a' w ≫ t) {b₀ : E} (hb₀ : b₀ ∈ B) :
    ∃ c : E → (Sp ℂ ⟶ Z), IsHolTo B c ∧ ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := by sorry
