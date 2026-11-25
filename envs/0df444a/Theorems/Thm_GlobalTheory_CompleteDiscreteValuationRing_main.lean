-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_main
-- name    : GlobalTheory.CompleteDiscreteValuationRing.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:12.68581+00:00
-- url     : https://prove2.me/theorems/09e50d41-e76e-4623-83c5-b54e8ae09b20
-- title:
--   Complete Discrete Valuation Ring: main
-- statement:
--   The Complete Discrete Valuation Ring construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L355-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L355-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing

theorem GlobalTheory.CompleteDiscreteValuationRing.main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W)
      (ψ' : R →+* W) (m : ℕ) (m' : ℕ) (k' : I → ℕ),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧
        IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧
        ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by sorry
