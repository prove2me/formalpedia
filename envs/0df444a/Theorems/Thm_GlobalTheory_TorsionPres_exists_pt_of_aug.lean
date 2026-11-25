-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPres_exists_pt_of_aug
-- name    : GlobalTheory.TorsionPres.exists_pt_of_aug
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:04.609492+00:00
-- url     : https://prove2.me/theorems/d3ea2d51-63f3-5b66-9fbf-b3a092d2d1c8
-- title:
--   Torsion Pres: exists pt of aug
-- statement:
--   The Torsion Pres construction uses the exists pt of aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L186-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L186-L210

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroup
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionPres
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Sp O)} [GrpObj G]

theorem GlobalTheory.TorsionPres.exists_pt_of_aug (C : Chart.Chart G) {A : Type} [CommRing A] [Algebra O A] (α : A →ₐ[O] O)
    (hα : ∀ a, IsUnit (α a) → IsUnit a) (z : specO O A ⟶ G) (hz : ptMap α ≫ z = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[O] A, z = Chart.pt C h ∧ α.comp h = Chart.eps C := by sorry
