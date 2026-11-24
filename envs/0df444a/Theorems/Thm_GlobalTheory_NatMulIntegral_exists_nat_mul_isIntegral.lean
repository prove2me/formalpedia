-- Prove2me | Theorems.Thm_GlobalTheory_NatMulIntegral_exists_nat_mul_isIntegral
-- name    : GlobalTheory.NatMulIntegral.exists_nat_mul_isIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:46.03106+00:00
-- url     : https://prove2.me/theorems/5e0f5135-c517-4817-b249-1e30c59f44c1
-- title:
--   Nat Mul Integral: exists nat mul is Integral
-- statement:
--   The Nat Mul Integral construction uses the exists nat mul is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNatSmulMem.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNatSmulMem.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulIntegral
open NumberField

theorem GlobalTheory.NatMulIntegral.exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by sorry
