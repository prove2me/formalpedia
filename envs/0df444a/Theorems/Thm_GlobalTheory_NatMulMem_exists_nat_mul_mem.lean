-- Prove2me | Theorems.Thm_GlobalTheory_NatMulMem_exists_nat_mul_mem
-- name    : GlobalTheory.NatMulMem.exists_nat_mul_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:29.706415+00:00
-- url     : https://prove2.me/theorems/280be09c-5092-45f9-b037-1e1a10ac11bf
-- title:
--   Nat Mul Mem: exists nat mul mem
-- statement:
--   The Nat Mul Mem construction uses the exists nat mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/Imports.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/Imports.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMem
open NumberField

theorem GlobalTheory.NatMulMem.exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by sorry
