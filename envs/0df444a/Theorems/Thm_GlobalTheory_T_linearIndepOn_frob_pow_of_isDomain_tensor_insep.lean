-- Prove2me | Theorems.Thm_GlobalTheory_T_linearIndepOn_frob_pow_of_isDomain_tensor_insep
-- name    : GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:28.94069+00:00
-- url     : https://prove2.me/theorems/4eed5ba3-db00-4ed6-b3ed-83d2ae3a6526
-- title:
--   T: linear Indep On frob pow of is Domain tensor insep
-- statement:
--   The T construction uses the linear Indep On frob pow of is Domain tensor insep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by sorry
