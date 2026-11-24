-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_isPullback_of_sq_eq_bot
-- name    : GlobalTheory.AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:26.868597+00:00
-- url     : https://prove2.me/theorems/6b070d7f-18e4-499d-8919-5784d4ba662b
-- title:
--   Affine Thickening: is Affine of is Pullback of sq eq bot
-- statement:
--   The Affine Thickening construction uses the is Affine of is Pullback of sq eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L323-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L323-L343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}

theorem GlobalTheory.AffineThickening.isAffine_of_isPullback_of_sq_eq_bot {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) (hsq : RingHom.ker β.hom ^ 2 = ⊥) {f : Y ⟶ Spec A} {i : Z ⟶ Y}
    {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Z] : IsAffine Y := by sorry
