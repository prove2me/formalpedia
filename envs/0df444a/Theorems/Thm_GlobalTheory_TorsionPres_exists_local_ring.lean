-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPres_exists_local_ring
-- name    : GlobalTheory.TorsionPres.exists_local_ring
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:14:56.55436+00:00
-- url     : https://prove2.me/theorems/b1702c8e-cbfe-5859-993b-53a1a9c004ee
-- title:
--   Torsion Pres: exists local ring
-- statement:
--   The Torsion Pres construction uses the exists local ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L212-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L212-L254

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

theorem GlobalTheory.TorsionPres.exists_local_ring (G : Over (Sp O)) [GrpObj G] (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (u : specO O S ⟶ G) (eS : S →ₐ[O] O)
      (x : Fin g → S),
      (∀ s, IsUnit (eS s) → IsUnit s) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A], ptMap ((Algebra.ofId O A).comp eS) ≫ u = 1) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (φ ψ : S →ₐ[O] A),
        ptMap φ ≫ u = ptMap ψ ≫ u → φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [Algebra O A] (α : A →ₐ[O] O), (∀ a, IsUnit (α a) → IsUnit a) →
        ∀ z : specO O A ⟶ G, ptMap α ≫ z = 1 → ∃ φ : S →ₐ[O] A, ptMap φ ≫ u = z) ∧
      RingHom.ker eS = Ideal.span (Set.range x) ∧
      (∀ j, ∃ v : S →ₐ[O] DualNumber O, (TrivSqZeroExt.fstHom O O O).comp v = eS ∧
        ∀ i, v (x i) = TrivSqZeroExt.inr (if i = j then 1 else 0)) ∧
      ∃ ρ : S →ₐ[O] MvPowerSeries (Fin g) (IsLocalRing.ResidueField O),
        ∀ i, ρ (x i) = MvPowerSeries.X i := by sorry
