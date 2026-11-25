-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_commGrpObj_weierstrassScheme
-- name    : GlobalTheory.T.exists_commGrpObj_weierstrassScheme
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:09.990444+00:00
-- url     : https://prove2.me/theorems/ac9ffefa-ab90-5dd9-b43d-09fa528cd0a7
-- title:
--   T: exists comm Grp Obj weierstrass Scheme
-- statement:
--   The T construction uses the exists comm Grp Obj weierstrass Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsCommGrpObjWeierstrassSchemeStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsCommGrpObjWeierstrassSchemeStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsCommGrpObjWeierstrassScheme
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsCommGrpObjWeierstrassSchemeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem GlobalTheory.T.exists_commGrpObj_weierstrassScheme : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ (η[schemeOver W].left = zero W ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) (hT : IsUnimodularSol (W.map ρ) T), (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧ Proportional T (diagXYZ (W.map ρ).toProjective P Q)) → ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP → y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P), ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN)) := by sorry
