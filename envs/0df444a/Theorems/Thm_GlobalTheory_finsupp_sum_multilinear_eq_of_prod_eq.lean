-- Prove2me | Theorems.Thm_GlobalTheory_finsupp_sum_multilinear_eq_of_prod_eq
-- name    : GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:36.859936+00:00
-- url     : https://prove2.me/theorems/58b3008d-6269-47d7-ad3c-11b6e699dfeb
-- title:
--   Global Theory: finsupp sum multilinear eq of prod eq
-- statement:
--   The Global Theory construction uses the finsupp sum multilinear eq of prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFiniteReproducingOfSubmodule.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFiniteReproducingOfSubmodule.lean#L19-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInterpolation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFiniteReproducingOfSubmodule
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

theorem GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : MultilinearMap ℂ (fun k => ↥(V k)) R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by sorry
