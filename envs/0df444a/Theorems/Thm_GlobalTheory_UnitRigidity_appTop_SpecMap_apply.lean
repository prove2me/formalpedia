-- Prove2me | Theorems.Thm_GlobalTheory_UnitRigidity_appTop_SpecMap_apply
-- name    : GlobalTheory.UnitRigidity.appTop_SpecMap_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:55.215604+00:00
-- url     : https://prove2.me/theorems/ea3f20f6-58fb-5f1c-bc2d-2cc5317e95ef
-- title:
--   Unit Rigidity: app Top Spec Map apply
-- statement:
--   The Unit Rigidity construction uses the app Top Spec Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L264-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L264-L269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
open scoped TensorProduct

theorem GlobalTheory.UnitRigidity.appTop_SpecMap_apply {R S : CommRingCat.{0}} (φ : R ⟶ S) {X : Scheme.{0}} (g : Spec R ⟶ X)
    (u : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom ((Spec.map φ ≫ g).appTop.hom u) =
      φ.hom ((Scheme.ΓSpecIso R).hom.hom (g.appTop.hom u)) := by sorry
