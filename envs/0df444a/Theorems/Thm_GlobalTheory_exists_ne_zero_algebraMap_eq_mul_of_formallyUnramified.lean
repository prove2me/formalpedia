-- Prove2me | Theorems.Thm_GlobalTheory_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified
-- name    : GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:59.121894+00:00
-- url     : https://prove2.me/theorems/cf52fb04-0700-4b0a-b2a7-58b1fe5ac779
-- title:
--   Global Theory: exists ne zero algebra Map eq mul of formally Unramified
-- statement:
--   The Global Theory construction uses the exists ne zero algebra Map eq mul of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA.lean#L7-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Algebra
open GlobalTheory

theorem GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified :
    ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D]
      [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 →
      ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by sorry
