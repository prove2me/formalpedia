-- Prove2me | Theorems.Thm_GlobalTheory_KeyFin_finite_preimage_of_isPullback_of_finite_base
-- name    : GlobalTheory.KeyFin.finite_preimage_of_isPullback_of_finite_base
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:24.889312+00:00
-- url     : https://prove2.me/theorems/bed25643-efa8-4fba-8761-fef01f4a369e
-- title:
--   Key Fin: finite preimage of is Pullback of finite base
-- statement:
--   The Key Fin construction uses the finite preimage of is Pullback of finite base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FinitePreimageOfIsPullbackOfFiniteBase.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FinitePreimageOfIsPullbackOfFiniteBase.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FinitePreimageOfIsPullbackOfFiniteBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.KeyFin

theorem GlobalTheory.KeyFin.finite_preimage_of_isPullback_of_finite_base :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by sorry
