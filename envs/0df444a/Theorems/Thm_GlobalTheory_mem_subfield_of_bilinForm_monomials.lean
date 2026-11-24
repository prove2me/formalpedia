-- Prove2me | Theorems.Thm_GlobalTheory_mem_subfield_of_bilinForm_monomials
-- name    : GlobalTheory.mem_subfield_of_bilinForm_monomials
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:50.143095+00:00
-- url     : https://prove2.me/theorems/e9f21a70-591a-4f8e-b29e-18a4a0c24c88
-- title:
--   Global Theory: mem subfield of bilin Form monomials
-- statement:
--   The Global Theory construction uses the mem subfield of bilin Form monomials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L51-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L51-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.mem_subfield_of_bilinForm_monomials :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by sorry
