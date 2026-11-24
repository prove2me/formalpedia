-- Prove2me | Theorems.Thm_GlobalTheory_NatMulMemUnitaryExistence_exists_nat_mul_mem
-- name    : GlobalTheory.NatMulMemUnitaryExistence.exists_nat_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:47.119844+00:00
-- url     : https://prove2.me/theorems/91cad792-3312-4928-a56c-1974e8fc6e71
-- title:
--   Nat Mul Mem Unitary Existence: exists nat mul mem
-- statement:
--   The Nat Mul Mem Unitary Existence construction uses the exists nat mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulMem.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulMem.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMemUnitaryExistence
open NumberField

theorem GlobalTheory.NatMulMemUnitaryExistence.exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : 𝓞 E, (a : E) = (k : E) * c := by sorry
