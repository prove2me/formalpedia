-- Prove2me | Theorems.Thm_GlobalTheory_exists_finset_mem_range_map_val
-- name    : GlobalTheory.exists_finset_mem_range_map_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:47.738611+00:00
-- url     : https://prove2.me/theorems/cf28148c-e67d-4495-8a78-978fe3b1c491
-- title:
--   Global Theory: exists finset mem range map val
-- statement:
--   The Global Theory construction uses the exists finset mem range map val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L35-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open Algebra.TensorProduct

theorem GlobalTheory.exists_finset_mem_range_map_val {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by sorry
