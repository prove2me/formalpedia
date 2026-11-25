-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_zerosIn_finite_one
-- name    : GlobalTheory.Mem.An.Model.zerosIn_finite_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:56.133633+00:00
-- url     : https://prove2.me/theorems/ab4c8a05-8b29-5bc6-b988-330ee0a0a45e
-- title:
--   Model: zeros In finite one
-- statement:
--   The Model construction uses the zeros In finite one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L120-L128

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

theorem GlobalTheory.Mem.An.Model.zerosIn_finite_one {q : ℕ} [NeZero q] (t T : ℝ) :
    (zerosIn (1 : DirichletCharacter ℂ q) t T).Finite := by sorry
