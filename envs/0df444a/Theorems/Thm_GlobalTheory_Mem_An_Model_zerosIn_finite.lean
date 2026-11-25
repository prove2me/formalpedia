-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_zerosIn_finite
-- name    : GlobalTheory.Mem.An.Model.zerosIn_finite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:16.940824+00:00
-- url     : https://prove2.me/theorems/722b198d-1fe1-44e7-b853-5d246e96161c
-- title:
--   Model: zeros In finite
-- statement:
--   The Model construction uses the zeros In finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L101-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model

theorem GlobalTheory.Mem.An.Model.zerosIn_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t T : ℝ) :
    (zerosIn χ t T).Finite := by sorry
