-- Prove2me | Theorems.Thm_GlobalTheory_exists_corner_unit_of_right_inverse
-- name    : GlobalTheory.exists_corner_unit_of_right_inverse
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:41.410813+00:00
-- url     : https://prove2.me/theorems/dddbf3a0-a060-4f4b-af31-c43a61ac9b12
-- title:
--   Global Theory: exists corner unit of right inverse
-- statement:
--   The Global Theory construction uses the exists corner unit of right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCornerUnitOfRightInverse.lean#L8-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCornerUnitOfRightInverse.lean#L8-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCornerUnitOfRightInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
open Polynomial

theorem GlobalTheory.exists_corner_unit_of_right_inverse :
    ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
      (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
        ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
      ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
        ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by sorry
