-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_tate_free_perfect
-- name    : GlobalTheory.PDivGroup.tate_free_perfect
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:43.09483+00:00
-- url     : https://prove2.me/theorems/4462336e-f2e3-4eff-a201-72189b848ec7
-- title:
--   PDiv Group: tate free perfect
-- statement:
--   The PDiv Group construction uses the tate free perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L456-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvEqOneOfForallPairing.lean#L456-L473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory

theorem GlobalTheory.PDivGroup.tate_free_perfect (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [IsDomain O]
    [IsIntegrallyClosed O] [Field C] [Algebra O C] [IsFractionRing O C] [IsAlgClosed C]
    [CharZero C] (G : PDivGroup p O) :
    (∀ n, Nat.card (G.A n →ₐ[O] O) = p ^ (n * G.height)) ∧
    (∀ n, Function.Surjective fun t : G.Tate => t.pt n) ∧
    (∀ (n : ℕ) (t : G.Tate), t.conv n = 1 ↔ ∃ s : G.Tate, (p : ℤ_[p]) ^ n • s = t) ∧
    (Module.Finite ℤ_[p] G.Tate ∧ Module.Free ℤ_[p] G.Tate ∧
      finrank ℤ_[p] G.Tate = G.height) ∧
    (∃ ζ : ℕ → O, ζ 0 = 1 ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧ ∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) ∧
    (∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n),
      (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) →
        Function.Bijective fun a : ℤ_[p] => (a • PDivGroup.muTate O ζ h0 h :
          (PDivGroup.mu p O).Tate)) ∧
    Function.Bijective (PDivGroup.pairing G O) ∧
    Function.Bijective (PDivGroup.pairing G O).flip := by sorry
