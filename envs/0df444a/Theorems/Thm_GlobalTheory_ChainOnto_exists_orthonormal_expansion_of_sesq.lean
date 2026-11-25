-- Prove2me | Theorems.Thm_GlobalTheory_ChainOnto_exists_orthonormal_expansion_of_sesq
-- name    : GlobalTheory.ChainOnto.exists_orthonormal_expansion_of_sesq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:35.549328+00:00
-- url     : https://prove2.me/theorems/57e31f01-66f0-44c7-9cae-db2af5a9d5ba
-- title:
--   Chain Onto: exists orthonormal expansion of sesq
-- statement:
--   The Chain Onto construction uses the exists orthonormal expansion of sesq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemRangeAdjointOfMemSpanEvaluationValues.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemRangeAdjointOfMemSpanEvaluationValues.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemRangeAdjointOfMemSpanEvaluationValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
open GlobalTheory GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.exists_orthonormal_expansion_of_sesq {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by sorry
