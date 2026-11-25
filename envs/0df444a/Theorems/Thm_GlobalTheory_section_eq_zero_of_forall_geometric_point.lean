-- Prove2me | Theorems.Thm_GlobalTheory_section_eq_zero_of_forall_geometric_point
-- name    : GlobalTheory.section_eq_zero_of_forall_geometric_point
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:19.085865+00:00
-- url     : https://prove2.me/theorems/594ebe83-ebb1-4427-beed-ee7b698f3be3
-- title:
--   Global Theory: section eq zero of forall geometric point
-- statement:
--   The Global Theory construction uses the section eq zero of forall geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SectionEqZeroOfForallGeometricPoint.lean#L96-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SectionEqZeroOfForallGeometricPoint.lean#L96-L114

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
open GlobalTheory

theorem GlobalTheory.section_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (H Y : Over (Spec (CommRingCat.of O))), IsFinite H.hom → Flat H.hom → IsReduced (specO O F ⊗ H).left → Flat Y.hom → ∀ (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W)), (∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) → f = 0 := by sorry
