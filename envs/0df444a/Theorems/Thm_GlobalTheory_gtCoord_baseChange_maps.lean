-- Prove2me | Theorems.Thm_GlobalTheory_gtCoord_baseChange_maps
-- name    : GlobalTheory.gtCoord_baseChange_maps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:45.660028+00:00
-- url     : https://prove2.me/theorems/9e282e9d-23fd-4374-a3fb-ba336f7d64c7
-- title:
--   Global Theory: gt Coord base Change maps
-- statement:
--   The Global Theory construction uses the gt Coord base Change maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L98-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L98-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
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
open GlobalTheory
open TorusExtBaseChange

theorem GlobalTheory.gtCoord_baseChange_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G), ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val := by sorry
