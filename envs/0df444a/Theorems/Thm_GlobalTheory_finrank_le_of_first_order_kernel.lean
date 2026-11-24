-- Prove2me | Theorems.Thm_GlobalTheory_finrank_le_of_first_order_kernel
-- name    : GlobalTheory.finrank_le_of_first_order_kernel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:34.185427+00:00
-- url     : https://prove2.me/theorems/5bc259e4-b757-4c6d-841f-207dc2fa2de9
-- title:
--   Global Theory: finrank le of first order kernel
-- statement:
--   The Global Theory construction uses the finrank le of first order kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExt.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExt.lean#L5-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.finrank_le_of_first_order_kernel (k V U : Type) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup U] [Module k U] [Module.Finite k U] (e : ℕ) (t u : V →ₗ[k] U)
    (h : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) :
    Module.finrank k V ≤ Module.finrank k U + e := by sorry
