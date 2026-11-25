-- Prove2me | Theorems.Thm_GlobalTheory_SmoothLocusBaseChange_main
-- name    : GlobalTheory.SmoothLocusBaseChange.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:43.61519+00:00
-- url     : https://prove2.me/theorems/dd48c30f-a5c3-55b7-850f-a3ccb94103f2
-- title:
--   Smooth Locus Base Change: main
-- statement:
--   The Smooth Locus Base Change construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LiftMulHomPullbackFst.lean#L53-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LiftMulHomPullbackFst.lean#L53-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothLocusBaseChange
open GlobalTheory.WeierstrassCurve

theorem GlobalTheory.SmoothLocusBaseChange.main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ (U' : (GlobalTheory.WeierstrassCurve.scheme (W.map f)).Opens) (_ : GrpObj (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (e : (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f))) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst _ _ ≫ U.ι = U'.ι ≫ GlobalTheory.WeierstrassCurve.mapHom W f rfl ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P h ⁻¹ᵁ U' ↔ ((W.map f).map ρ).toProjective.Nonsingular P) ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) Q), x.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P hP → y.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) (((W.map f).map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))]).left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ _ h) := by sorry
