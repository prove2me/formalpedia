-- Prove2me | Theorems.Thm_GlobalTheory_mem_monomialExponents
-- name    : GlobalTheory.mem_monomialExponents
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:17.664745+00:00
-- url     : https://prove2.me/theorems/0aa332bd-a3fa-42e9-8812-0411fcebd7ea
-- title:
--   Global Theory: mem monomial Exponents
-- statement:
--   The Global Theory construction uses the mem monomial Exponents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L37-L39

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

theorem GlobalTheory.mem_monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := by sorry
