-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_not_mem_mul_mem_sq_of_pderiv_mem
-- name    : GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:36:59.847214+00:00
-- url     : https://prove2.me/theorems/6386414e-4c73-46f6-87e5-faddc5068e52
-- title:
--   T: exists not mem mul mem sq of pderiv mem
-- statement:
--   The T construction uses the exists not mem mul mem sq of pderiv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMemStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMemStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by sorry
