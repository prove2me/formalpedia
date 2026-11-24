-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_exists_dividedPowers
-- name    : GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:42.858819+00:00
-- url     : https://prove2.me/theorems/de3f8174-0815-4c2f-b60b-82d1ff83bdf2
-- title:
--   Torsion Free Divided Powers: exists divided Powers
-- statement:
--   The Torsion Free Divided Powers construction uses the exists divided Powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L63-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L63-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.TorsionFreeDividedPowers
open DividedPowers

theorem GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers :
    ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R],
    (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)},
      (m.factorial : R) * γ₀.dpow m y = y ^ m := by sorry
