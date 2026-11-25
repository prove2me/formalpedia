-- Prove2me | Theorems.Thm_GlobalTheory_mem_primeIdealOf_iff_evaluation_eq_zero
-- name    : GlobalTheory.mem_primeIdealOf_iff_evaluation_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:54.658179+00:00
-- url     : https://prove2.me/theorems/d577c3b6-47c5-4730-b7b1-1cf880f8747a
-- title:
--   Global Theory: mem prime Ideal Of iff evaluation eq zero
-- statement:
--   The Global Theory construction uses the mem prime Ideal Of iff evaluation eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L422-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L422-L428

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

theorem GlobalTheory.mem_primeIdealOf_iff_evaluation_eq_zero {Z : Scheme.{0}} {V : Z.Opens}
    (hV : IsAffineOpen V) {z : Z} (hz : z ∈ V) (a : Γ(Z, V)) :
    a ∈ (hV.primeIdealOf ⟨z, hz⟩).asIdeal ↔ Z.evaluation V z hz a = 0 := by sorry
