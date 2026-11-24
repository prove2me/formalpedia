-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_of_forall_algHom_eq
-- name    : GlobalTheory.mem_range_of_forall_algHom_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:27.425114+00:00
-- url     : https://prove2.me/theorems/81ad2ad0-a64e-4f37-ba4f-ba73b4d79323
-- title:
--   Global Theory: mem range of forall alg Hom eq
-- statement:
--   The Global Theory construction uses the mem range of forall alg Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemRangeOfForallAlgHomEq.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemRangeOfForallAlgHomEq.lean#L8-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
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
open Polynomial

theorem GlobalTheory.mem_range_of_forall_algHom_eq :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by sorry
