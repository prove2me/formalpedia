-- Prove2me | Theorems.Thm_GlobalTheory_TorsionIntegral_exists_finset_extend
-- name    : GlobalTheory.TorsionIntegral.exists_finset_extend
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:26:03.450433+00:00
-- url     : https://prove2.me/theorems/87048c2c-6afc-54fe-a38d-dc387f6d164d
-- title:
--   Torsion Integral: exists finset extend
-- statement:
--   The Torsion Integral construction uses the exists finset extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L21-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L21-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral

theorem GlobalTheory.TorsionIntegral.exists_finset_extend {V F : Type} [CommRing V] [Field F] [Algebra V F]
    (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom] (p : Spec (CommRingCat.of F) ⟶ B.left)
    (hp : p ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ S : Finset F, ∀ (W : Type) [CommRing W] [IsDomain W] [ValuationRing W] [Algebra V W] [Algebra W F]
      [IsScalarTower V W F], Function.Injective (algebraMap W F) →
      (∀ x ∈ S, ∃ a b : W, b ≠ 0 ∧ x * algebraMap W F b = algebraMap W F a) →
      ∃ l : Spec (CommRingCat.of W) ⟶ B.left, Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ l = p ∧
        l ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap V W)) := by sorry
