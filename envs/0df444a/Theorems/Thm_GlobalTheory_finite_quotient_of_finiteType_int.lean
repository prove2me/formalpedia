-- Prove2me | Theorems.Thm_GlobalTheory_finite_quotient_of_finiteType_int
-- name    : GlobalTheory.finite_quotient_of_finiteType_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:25.056516+00:00
-- url     : https://prove2.me/theorems/da35e724-ed00-582e-9211-c5ca42ac0a49
-- title:
--   Global Theory: finite quotient of finite Type int
-- statement:
--   The Global Theory construction uses the finite quotient of finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L267-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L267-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct

theorem GlobalTheory.finite_quotient_of_finiteType_int {A : Type*} [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : Finite (A ⧸ m) := by sorry
