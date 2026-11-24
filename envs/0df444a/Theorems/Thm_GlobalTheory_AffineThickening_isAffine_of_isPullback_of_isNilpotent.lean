-- Prove2me | Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_isPullback_of_isNilpotent
-- name    : GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:58:02.28226+00:00
-- url     : https://prove2.me/theorems/e6ec2642-aa1b-4914-9f13-a955039892b9
-- title:
--   Affine Thickening: is Affine of is Pullback of is Nilpotent
-- statement:
--   The Affine Thickening construction uses the is Affine of is Pullback of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L345-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean#L345-L366

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

theorem GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) : ∀ {C : CommRingCat.{u}} (β : CommRingCat.of A ⟶ C),
      Function.Surjective β → RingHom.ker β.hom = J → ∀ {Y Z : Scheme.{u}}
      {f : Y ⟶ Spec (.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}, IsPullback i f' f (Spec.map β) →
      IsAffine Z → IsAffine Y := by sorry
