-- Prove2me | Theorems.Thm_GlobalTheory_over_points_ext_of_injective
-- name    : GlobalTheory.over_points_ext_of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:33.438918+00:00
-- url     : https://prove2.me/theorems/c335e265-3d45-4784-b2e8-d72424e29f02
-- title:
--   Global Theory: over points ext of injective
-- statement:
--   The Global Theory construction uses the over points ext of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/OverPointsExtOfInjective.lean#L11-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/OverPointsExtOfInjective.lean#L11-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_OverPointsExtOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem GlobalTheory.over_points_ext_of_injective (S : Scheme.{0}) (G : Over S) [IsSeparated G.hom]
    (W F : Type) [CommRing W] [CommRing F] (φ : W →+* F) (hφ : Function.Injective φ)
    (p : Spec (CommRingCat.of W) ⟶ S) (y y' : Over.mk p ⟶ G)
    (h : (Spec.map (CommRingCat.ofHom φ)) ≫ y.left = (Spec.map (CommRingCat.ofHom φ)) ≫ y'.left) :
    y = y' := by sorry
