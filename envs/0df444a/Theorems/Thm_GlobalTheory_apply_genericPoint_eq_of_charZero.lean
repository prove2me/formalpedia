-- Prove2me | Theorems.Thm_GlobalTheory_apply_genericPoint_eq_of_charZero
-- name    : GlobalTheory.apply_genericPoint_eq_of_charZero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:55.098403+00:00
-- url     : https://prove2.me/theorems/7651486c-f3c0-47e6-b780-7590169bb20a
-- title:
--   Global Theory: apply generic Point eq of char Zero
-- statement:
--   The Global Theory construction uses the apply generic Point eq of char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L442-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L442-L447

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
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.apply_genericPoint_eq_of_charZero {R : CommRingCat.{0}} [IsDomain R] [CharZero R]
    (g : Spec R ⟶ Spec (.of ℤ)) : g (genericPoint (Spec R)) = genericPoint (Spec (.of ℤ)) := by sorry
