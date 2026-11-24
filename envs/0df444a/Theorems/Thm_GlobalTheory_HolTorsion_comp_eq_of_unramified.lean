-- Prove2me | Theorems.Thm_GlobalTheory_HolTorsion_comp_eq_of_unramified
-- name    : GlobalTheory.HolTorsion.comp_eq_of_unramified
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:52.273944+00:00
-- url     : https://prove2.me/theorems/cf7da9d5-9f9e-4486-a7b2-fa9f77a6e4d5
-- title:
--   Hol Torsion: comp eq of unramified
-- statement:
--   The Hol Torsion construction uses the comp eq of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L120-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionEqAndWeilIsOfIsHolTo.lean#L120-L137

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

theorem GlobalTheory.HolTorsion.comp_eq_of_unramified {N X : Scheme.{0}} (q : N ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
    [IsSeparated q] {c : E → (Sp ℂ ⟶ pullback q q)} (hc : IsHolTo B c) (hB : IsPreconnected B) {b₀ b : E}
    (hb₀ : b₀ ∈ B) (hb : b ∈ B) (h₀ : c b₀ ≫ pullback.fst q q = c b₀ ≫ pullback.snd q q) :
    c b ≫ pullback.fst q q = c b ≫ pullback.snd q q := by sorry
