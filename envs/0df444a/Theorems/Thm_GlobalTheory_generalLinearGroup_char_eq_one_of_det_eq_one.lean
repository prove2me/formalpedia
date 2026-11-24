-- Prove2me | Theorems.Thm_GlobalTheory_generalLinearGroup_char_eq_one_of_det_eq_one
-- name    : GlobalTheory.generalLinearGroup_char_eq_one_of_det_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:07.987594+00:00
-- url     : https://prove2.me/theorems/68725e75-f958-4319-9c78-fd60ea2c0fb6
-- title:
--   Global Theory: general Linear Group char eq one of det eq one
-- statement:
--   The Global Theory construction uses the general Linear Group char eq one of det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L403-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L403-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.generalLinearGroup_char_eq_one_of_det_eq_one :
    ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ) (A : Type) [CommGroup A]
      (ψ : GL (Fin r) R →* A), (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 4 ≤ Nat.card (R ⧸ 𝔪)) →
      ∀ g : GL (Fin r) R, (g : Matrix (Fin r) (Fin r) R).det = 1 → ψ g = 1 := by sorry
