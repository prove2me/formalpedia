-- Prove2me | Theorems.Thm_GlobalTheory_finiteType_int_sections
-- name    : GlobalTheory.finiteType_int_sections
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:18.570597+00:00
-- url     : https://prove2.me/theorems/b048c4e8-bafa-4d49-b0d6-0c5873e41a56
-- title:
--   Global Theory: finite Type int sections
-- statement:
--   The Global Theory construction uses the finite Type int sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L398-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L398-L406

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem GlobalTheory.finiteType_int_sections {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ)) [LocallyOfFiniteType π]
    {V : Z.Opens} (hV : IsAffineOpen V) : Algebra.FiniteType ℤ Γ(Z, V) := by sorry
