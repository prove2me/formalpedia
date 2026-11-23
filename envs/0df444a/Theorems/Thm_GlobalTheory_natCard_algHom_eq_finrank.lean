-- Prove2me | Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank
-- name    : GlobalTheory.natCard_algHom_eq_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:59.133183+00:00
-- url     : https://prove2.me/theorems/ef122199-d73d-462c-bab7-42f5df56d0ab
-- title:
--   Global Theory: nat Card alg Hom eq finrank
-- statement:
--   The Global Theory construction uses the nat Card alg Hom eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L81-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable (R S)

theorem GlobalTheory.natCard_algHom_eq_finrank [Nontrivial R] : Nat.card (S →ₐ[R] E) = finrank R S := by sorry
