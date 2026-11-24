-- Prove2me | Theorems.Thm_GlobalTheory_finite_algHom_of_isFiniteSplit
-- name    : GlobalTheory.finite_algHom_of_isFiniteSplit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:26.784339+00:00
-- url     : https://prove2.me/theorems/9502b67a-1463-4f24-81ae-dd475985a879
-- title:
--   Global Theory: finite alg Hom of is Finite Split
-- statement:
--   The Global Theory construction uses the finite alg Hom of is Finite Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L65-L67

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
variable (R S)

theorem GlobalTheory.finite_algHom_of_isFiniteSplit : Finite (S →ₐ[R] E) := by sorry
