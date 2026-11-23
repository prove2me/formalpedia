-- Prove2me | Theorems.Thm_GlobalTheory_realExtBilin_tmul
-- name    : GlobalTheory.realExtBilin_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:54.245223+00:00
-- url     : https://prove2.me/theorems/b2b64090-345b-4665-992a-8b4bc72c16fe
-- title:
--   Global Theory: real Ext Bilin tmul
-- statement:
--   The Global Theory construction uses the real Ext Bilin tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L269-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.realExtBilin_tmul (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s t : ℝ) (x y : X) :
    realExtBilin B (s ⊗ₜ x) (t ⊗ₜ y) = s * t * B x y := by sorry
