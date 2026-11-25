-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Lib_isFF_iff
-- name    : GlobalTheory.Nef.Lib.isFF_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:16.218739+00:00
-- url     : https://prove2.me/theorems/c66e86d6-085c-407d-a111-1c62aae652de
-- title:
--   Lib: is FF iff
-- statement:
--   The Lib construction uses the is FF iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L66-L66

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped IntermediateField Polynomial
open GlobalTheory GlobalTheory.Nef
variable {k F : Type} [Field k] [Field F] [Algebra k F]
open GlobalTheory.Nef.Lib
open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField

theorem GlobalTheory.Nef.Lib.isFF_iff : IsFF k F ↔ IsFunctionField k F := by sorry
