-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_notMem_forall_mem
-- name    : GlobalTheory.exists_prime_notMem_forall_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:51:40.976695+00:00
-- url     : https://prove2.me/theorems/31ecaddf-5779-4c01-9df8-ea68abcfb782
-- title:
--   Global Theory: exists prime not Mem forall mem
-- statement:
--   The Global Theory construction uses the exists prime not Mem forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L49-L62

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

theorem GlobalTheory.exists_prime_notMem_forall_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {f : A}
    {q : Ideal A} (hq : q.IsPrime) (hf : f ∉ q) : ∃ Q : Ideal A, Q.IsPrime ∧ f ∉ Q ∧
      ∀ P : Ideal (A ⧸ Q), P.IsPrime → P ≠ ⊥ → Ideal.Quotient.mk Q f ∈ P := by sorry
