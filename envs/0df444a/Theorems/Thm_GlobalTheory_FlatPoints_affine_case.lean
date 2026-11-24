-- Prove2me | Theorems.Thm_GlobalTheory_FlatPoints_affine_case
-- name    : GlobalTheory.FlatPoints.affine_case
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:39.177967+00:00
-- url     : https://prove2.me/theorems/96333ae3-f3fb-4b2d-a059-c70d6bff2b89
-- title:
--   Flat Points: affine case
-- statement:
--   The Flat Points construction uses the affine case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SectionEqZeroOfForallGeometricPoint.lean#L46-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SectionEqZeroOfForallGeometricPoint.lean#L46-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlatPoints

theorem GlobalTheory.FlatPoints.affine_case (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)]
    (H Y : Over (Spec (CommRingCat.of O))) (e : specO O A ≅ H) [Flat Y.hom]
    (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W))
    (h : ∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) : f = 0 := by sorry
