-- Prove2me | Theorems.Thm_GlobalTheory_hom_ext_of_fromSpecStalk
-- name    : GlobalTheory.hom_ext_of_fromSpecStalk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:30.206262+00:00
-- url     : https://prove2.me/theorems/83ae4847-4abe-48f0-bb0e-4e09eecddcfe
-- title:
--   Global Theory: hom ext of from Spec Stalk
-- statement:
--   The Global Theory construction uses the hom ext of from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L15-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L15-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory

theorem GlobalTheory.hom_ext_of_fromSpecStalk {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ x, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by sorry
