-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_SpecMap_fromSpecStalk_closedPoint
-- name    : GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:56.959169+00:00
-- url     : https://prove2.me/theorems/49820ee1-8e19-41c5-8fed-4998def79c94
-- title:
--   Tangent Crit: Spec Map from Spec Stalk closed Point
-- statement:
--   The Tangent Crit construction uses the Spec Map from Spec Stalk closed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L232-L236

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u

theorem GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by sorry
