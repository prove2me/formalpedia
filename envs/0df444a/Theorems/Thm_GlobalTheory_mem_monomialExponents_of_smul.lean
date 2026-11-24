-- Prove2me | Theorems.Thm_GlobalTheory_mem_monomialExponents_of_smul
-- name    : GlobalTheory.mem_monomialExponents_of_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:28.392845+00:00
-- url     : https://prove2.me/theorems/c281793a-af16-4745-942d-e64e435b97d4
-- title:
--   Global Theory: mem monomial Exponents of smul
-- statement:
--   The Global Theory construction uses the mem monomial Exponents of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSubfieldOfBilinFormBasisMonomials.lean#L41-L49

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

theorem GlobalTheory.mem_monomialExponents_of_smul {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by sorry
