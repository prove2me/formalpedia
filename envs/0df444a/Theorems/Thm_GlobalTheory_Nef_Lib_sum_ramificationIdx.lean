-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Lib_sum_ramificationIdx
-- name    : GlobalTheory.Nef.Lib.sum_ramificationIdx
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:39.756271+00:00
-- url     : https://prove2.me/theorems/84e12053-e158-553e-acb9-612debb792be
-- title:
--   Lib: sum ramification Idx
-- statement:
--   The Lib construction uses the sum ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean#L133-L147

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

theorem GlobalTheory.Nef.Lib.sum_ramificationIdx [IsAlgClosed k] {E : Type} [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [IsFunctionField k F] [IsFunctionField k E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (v : GroundTheory.FunctionField.Place k F) :
    ∑ w ∈ (v.finite_liesOver (K' := E)).toFinset, w.ramificationIdx v = Module.finrank F E := by sorry
