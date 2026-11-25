-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Lib_ord_toRing
-- name    : GlobalTheory.Nef.Lib.ord_toRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:18.897714+00:00
-- url     : https://prove2.me/theorems/c62e8603-0bd7-44b2-b5fe-303a508305cb
-- title:
--   Lib: ord to Ring
-- statement:
--   The Lib construction uses the ord to Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L93-L94

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

theorem GlobalTheory.Nef.Lib.ord_toRing [IsFunctionField k F] (v : Nef.Place k F) (x : F) : (toRing v).ord x = ord v x := by sorry
