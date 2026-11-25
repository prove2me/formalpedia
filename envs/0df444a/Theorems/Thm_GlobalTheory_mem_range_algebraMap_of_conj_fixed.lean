-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_algebraMap_of_conj_fixed
-- name    : GlobalTheory.mem_range_algebraMap_of_conj_fixed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:04.071941+00:00
-- url     : https://prove2.me/theorems/6915b306-3fae-4a8a-acc5-86cfe65fa294
-- title:
--   Global Theory: mem range algebra Map of conj fixed
-- statement:
--   The Global Theory construction uses the mem range algebra Map of conj fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemRangeAlgebraMapOfConjFixed.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemRangeAlgebraMapOfConjFixed.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemRangeAlgebraMapOfConjFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.mem_range_algebraMap_of_conj_fixed (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : E) (he : σ e = e) :
    ∃ c : F, algebraMap F E c = e := by sorry
