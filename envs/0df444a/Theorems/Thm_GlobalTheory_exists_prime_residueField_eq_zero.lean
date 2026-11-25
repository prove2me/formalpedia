-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_residueField_eq_zero
-- name    : GlobalTheory.exists_prime_residueField_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:05.130803+00:00
-- url     : https://prove2.me/theorems/42a1c6b3-ae3d-4535-b536-1f431b6d4756
-- title:
--   Global Theory: exists prime residue Field eq zero
-- statement:
--   The Global Theory construction uses the exists prime residue Field eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L430-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L430-L438

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

theorem GlobalTheory.exists_prime_residueField_eq_zero {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ))
    [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z)) :
    ∃ p : ℕ, p.Prime ∧ (p : Z.residueField z) = 0 := by sorry
