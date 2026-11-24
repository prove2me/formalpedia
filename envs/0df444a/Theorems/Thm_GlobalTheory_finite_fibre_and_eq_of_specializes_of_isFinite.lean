-- Prove2me | Theorems.Thm_GlobalTheory_finite_fibre_and_eq_of_specializes_of_isFinite
-- name    : GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:34.033357+00:00
-- url     : https://prove2.me/theorems/b3dda5a2-ae06-43ac-928a-6f7dc2f2f323
-- title:
--   Global Theory: finite fibre and eq of specializes of is Finite
-- statement:
--   The Global Theory construction uses the finite fibre and eq of specializes of is Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFibreAndEqOfSpecializesOfIsFinite.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFibreAndEqOfSpecializesOfIsFinite.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFibreAndEqOfSpecializesOfIsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by sorry
