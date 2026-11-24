-- Prove2me | Theorems.Thm_GlobalTheory_multilinear_sum_eq_of_prod_fun_eq
-- name    : GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:21.20185+00:00
-- url     : https://prove2.me/theorems/649bff89-12de-4691-963a-b21e48a3cf6f
-- title:
--   Global Theory: multilinear sum eq of prod fun eq
-- statement:
--   The Global Theory construction uses the multilinear sum eq of prod fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MultilinearSumEqOfProdFunEq.lean#L8-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MultilinearSumEqOfProdFunEq.lean#L8-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FinsetFunctionsRecoveredFromValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MultilinearSumEqOfProdFunEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
    {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l) :
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) =
        a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by sorry
