-- Prove2me | Theorems.Thm_GlobalTheory_FockAlg_injective_of_pderiv
-- name    : GlobalTheory.FockAlg.injective_of_pderiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:21.236339+00:00
-- url     : https://prove2.me/theorems/7c7cd0ad-8d90-4e65-a566-1e134b374d50
-- title:
--   Fock Alg: injective of pderiv
-- statement:
--   The Fock Alg construction uses the injective of pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InjectiveOfMapPderivEqAndMapOneNeZero.lean#L7-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InjectiveOfMapPderivEqAndMapOneNeZero.lean#L7-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InjectiveOfMapPderivEqAndMapOneNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FockAlg
open MvPolynomial

theorem GlobalTheory.FockAlg.injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by sorry
